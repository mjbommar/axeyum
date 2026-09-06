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
| QF_UF | `b32377dc5` | 190 | 200 | 95.0% | 190 / 0 / 10 | 10 |
| UF | `b32377dc5` | 85 | 93 | 91.4% | 61 / 24 / 32 | 8 |
| QF_ABV | `9914a1c0e` | 179 | 197 | 90.9% | 178 / 1 / 19 | 18 |
| QF_RDL | `b32377dc5` | 128 | 154 | 83.1% | 127 / 1 / 27 | 26 |
| QF_LIA | `b32377dc5` | 112 | 139 | 80.6% | 110 / 2 / 29 | 27 |
| QF_IDL | `b32377dc5` | 86 | 123 | 69.9% | 84 / 2 / 39 | 37 |
| QF_UFLIA | `5c9b3a7c2` | 123 | 180 | 68.3% | 123 / 0 / 57 | 57 |
| QF_LRA | `5c9b3a7c2` | 93 | 145 | 64.1% | 93 / 0 / 52 | 52 |
| QF_NIA | `9914a1c0e` | 39 | 87 | 44.8% | 26 / 13 / 61 | 48 |

Total gap to parity: **290 files, down from 356** at the start of the plan
(ours 1,416 of 1,706 reference decisions). S1 alone moved 65 files (QF_IDL
+16, QF_RDL +21, QF_UF +28); S4 moved 3 (QF_LRA +2, QF_UFLIA +1). The two
QF_LIA files that appeared lost under S1 were traced by S1b to S2's admission
preflight, not to the watched literals (see the S1b status file). QF_SLIA,
QF_BV, QF_ABV and QF_NIA have not been re-measured since `9914a1c0e` because
no landed slice targets them yet.

**What the census changed** ([note](../research/11-design-review/2026-09-05-parity-loss-census.md)):
of 403 losses, 217 are admission declines on constants, 137 search timeouts,
41 other, 6 unsupported shapes, 2 parser rejects. QF_IDL's 46 of 54 were the
S1/S2 signature and have largely converted. UF and QF_UF's 70 were one
admission cap on eager Ackermann expansion with no timeouts; S11a is on it.
QF_SLIA and QF_NIA both hit the 32-bit int-blast width ladder, a shared
S11/S12 target not previously named. One QF_LIA file overflows `i128` inside
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
1. Merge S1b, S9, S11a from their branches after the push freeze (S9 will
   conflict with the CAS lanes in `scripts/tests/mutation_controls.py`; take
   the sorted union and run that harness's self-suite); run each's full gate
   list on `main` after merge, clippy included (the composition failure of
   2026-09-06 was a clippy size lint, not a compile error). Then run the full
   200-file QF_UF and UF sweeps S11a did not run.
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
is authorized before it.

### 2.1 Difference logic: QF_IDL and QF_RDL, 101 files (measured)

**Cause.** `CdclT::unit_propagate`
(`crates/axeyum-solver/src/cdclt.rs:702`) is a full clause-database rescan per
fixpoint pass with no watch lists and no blocking literals, and it clones the
reason clause on every implication. On the five traced QF_IDL timeouts it is
19.4 s of a 24 s budget (87% of wall) with the theory at 0 ms
([profiles](../research/11-design-review/2026-09-05-arith-timeout-profiles.md)).
The 2026-08-21 diagnosis's "dl-online runs out of clock" was this function.

**Second cause.** Dispatch overrun: `dl-online` spends 18 to 21 s, then
`lia-dpll` spends a fixed ~8 s declining on a size constant it could have
evaluated at t = 0, so the sum exceeds the budget and the watchdog kills the
process before any statistics print (3 of 5 traced IDL files). The
2026-08-21 diagnosis priced the reserve at 6 s; today's measurement says ~8 s.

**Lever.** Two-watched-literal propagation with blocking literals inside
`CdclT`, ported verbatim from `proof_sat.rs`'s `Watch`/`ClauseHeader` design so
the later engine unification is a deletion rather than a reconciliation
([memo §6](adr-1701-slice-2-design-2026-09-05.md)). Separately, make
`lia-dpll` evaluate its size admission before consuming its reserve.

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
A further 29 QF_LRA files are refused at the 1,024-atom admission cap, which
the diagnosis measured as load-bearing protection (removing it: 0 new
decides, 54 memory aborts).

**Lever.** (a) Warm-start each final check from the previous tableau instead
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
decides 6 of those 26. Today's +9 came from the widened interface; the
remaining 58 have not been re-censused since.

**Lever.** (a) Re-census after today's changes; (b) ADR-1702 slice 2:
`Value::Int` and the SMT-LIB integer-literal parser gain the same opt-in
wide path the simplex has (+6 measured against cvc5); (c) the LRA levers
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
other (11 bounded-width-32 model incompleteness, 2 divergence). Full
detail: [parity loss census](../research/11-design-review/2026-09-05-parity-loss-census.md).

### 2.5 Uninterpreted functions: UF, 32 theirs / 24 ours; QF_UF, 38 theirs / 0 ours (census needed)

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
(route `qf-bv`) / 3 the same bound-64 CEGAR shape as UF. Neither division
has a single search-timeout file; 2.1's fix lands nothing here. Full
detail: [parity loss census](../research/11-design-review/2026-09-05-parity-loss-census.md).

### 2.6 Linear integers: QF_LIA, 27 theirs / 2 ours (census needed)

**What is known.** QF_LIA runs the LIA DPLL(T) driver (`dpll_lia.rs`), the
same family as QF_UFLIA, plus cuts. It gained one file today with the
reference unchanged. The 2026-08-21 core-minimisation fix (ADR-0538) moved
QF_UFLIA +22 and QF_LIA 0, which says QF_LIA's losses are not wide theory
cores.

**Lever.** Census. Expect a split between search timeouts (2.1's fix) and
cut-generation limits (a slice on the Gomory/branching budget, scored on the
27).

**Census (S3, 2026-09-05/06).** QF_LIA 27/27 losses classified: 15
admission-decline (`lia-dpll`'s pre-SAT resource boundary, the same family
as QF_IDL's dominant class), 4 search-timeout, 4 other
(explain-corpus-crash on large files; `smtcomp_cli` itself timed out
normally on all four), 3 other (branch-and-bound node-cap incompleteness),
1 other (i128 overflow in the exact-rational simplex -- a second S9 data
point beyond QF_UFLIA's parser case). Admission-decline outweighs
search-timeout more than 3:1. Full detail: [parity loss census](../research/11-design-review/2026-09-05-parity-loss-census.md).

### 2.7 Arrays over bit-vectors: QF_ABV, 19 theirs / 1 ours (census needed)

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

| # | Slice | Division(s) | Scoring files | Exit criterion | Gate |
|---|---|---|---|---|---|
| S1 | **Two-watched-literal propagation in `CdclT`**, blocking literals, ported verbatim from `proof_sat.rs`; no trait, caller or proof change | QF_IDL, QF_RDL, QF_UF, UF, QF_LIA, QF_LRA (Boolean part) | 50-file IDL population; 33-file LRA population | `TheoryLayerStats::boolean_propagate` falls on the 5 traced IDL files; IDL population decided rises from 0; zero verdict changes | solver `--lib --features full`, corpus sweep, cdclt suites, z3 fuzzes, frontier, then `parity-run.sh QF_IDL` and `QF_RDL` on an idle host |
| S2 | **Dispatch overrun fix**: `lia-dpll` evaluates its size admission before consuming its reserve; a declined route's budget returns to the pool | QF_IDL, QF_RDL, QF_LRA | the 3 of 5 traced IDL files that print no stats | every timeout prints a `; theory-layer` line; no verdict changes | route-trace tests, corpus sweep |
| S3 | **Loss census** for QF_UF, UF, QF_LIA, QF_ABV, QF_SLIA, QF_BV, QF_UFLIA: classify every reference-only file | the six censused divisions plus QF_UFLIA | one TSV per division with class, declining route, dominant stage; committed lists | measurement only | none (docs and artifacts) |
| S4 | **Simplex warm start** across final checks, and **implied-bound propagation** through the propagate hook | QF_LRA, QF_UFLIA, QF_LIA | 33-file LRA population; QF_UFLIA reference-only list | `theory_final_check_ms` per call and call count both fall on the 5 traced LRA files; LRA population decided rises from 5 | as S1 plus `parity-run.sh QF_LRA`, `QF_UFLIA` |
| S5 | **ADR: the proof contract under theory lemmas** (two streams, assumptions counted), then implement | all CDCL(T) divisions | none; a contract | a CDCL(T) `unsat` produces an artifact whose theory assumptions are enumerable and counted | evidence suites |
| S6 | **Reason representation** in the native core (`Option<CRef>` → tagged `Reason`), measured alone | prerequisite for S7 | criterion `proof_sat_solve_php_6_7`; 20 p4dfa CNFs | within the noise band; p4dfa decided unchanged | cnf suites, corpus |
| S7 | **Move CDCL(T) onto the native core** behind the measured hooks; `TheoryLayerStats` ported first; `CdclT::new` signature preserved | every theory division | full board | `cdclt_solve_php_6_7` closes most of the gap to `proof_sat_solve_php_6_7`; every verdict unchanged; then the full eleven-division parity sweep | everything in S1 plus the full sweep |
| S8 | **Native-core throughput**: profile propagate/analyze on p4dfa CNF by counters; arena locality, `reduce_db` tiering, restarts, in measured order | QF_BV first, all after S7 | 113 p4dfa CNFs at 20 s; the 6 Bitwuzla-only files | conflicts/s ratio to Kissat rises from 0.6 toward 1; p4dfa decided rises from 6 toward 11 | gate (b) rerun, `parity-run.sh QF_BV` |
| S9 | **ADR-1702 slice 2**: `Value::Int` and the integer-literal parser gain the opt-in wide path | QF_UFLIA (+6 measured), QF_LIA, QF_NIA | the 26 rejected QF_UFLIA files | they reach the solver; 6 decide; zero verdict changes | ir and solver suites, z3 fuzzes, corpus |
| S10 | **Dynamic atom registration** via the widened trait, retiring driver side tables; then revisit the 1,024-atom cap as a memory budget | QF_LRA | the 29 atom-cap refusals | a measured memory budget replaces the constant; refusals convert or are reported as memory-bound with the number | as S4 |
| S11 | **Per-division capability slices from the census**: nested arrays or ADR-0085 boundary shapes (QF_ABV); certifiable string refutations (QF_SLIA); bounded finite-model finding (UF); cut budget (QF_LIA) | as named | each division's committed loss list | division count rises by the classified files | division suites plus its `parity-run.sh` |
| S12 | **NIA coefficient-width rung** via eager small-domain product split | QF_NIA | the 32 one-live-rung files | decided rises from 0 on those 32; zero verdict changes | nia suites, corpus, `parity-run.sh QF_NIA` |

Dependencies: S1, S2, S3 start now and are independent. S4 needs S1's
instrument unchanged (it is) and starts now. S5 gates S7. S6 and S5 are
independent and can run together. S8 after S7 so the gain reaches every
division. S9, S10, S11, S12 are independent of the engine work and are
scheduled by census result.

## 5. What "parity or better" means per division, and when to stop

| Division | Parity count | Realistic path in this plan | Stop condition |
|---|---:|---|---|
| QF_SLIA | 194 | S11 string refutations, 7 files | at or above 194 with 0 disagreements |
| QF_BV | 194 | S8, 6 files, Bitwuzla-only since July | at or above 194 |
| UF | 93 | S1 plus S11 finite-model finding | at or above 93; the 24 axeyum-only stay |
| QF_ABV | 197 | S1 plus S11 array shapes | at or above 197 |
| QF_LIA | 139 | S1, S4, S11 cuts | at or above 139 |
| QF_UF | 200 | S1 plus census | 200 |
| QF_RDL | 154 | S1, S2 | at or above 154 |
| QF_UFLIA | 180 | S1, S4, S9 | at or above 180 |
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

## 7. What this plan does not claim

- Ratios against cvc5 on QF_NIA are not a stable target; the axeyum count is.
- The census divisions have no cause named yet; their slices are scheduled by
  the census, not by this document.
- The 24 s budget is the competition convention; nothing here says what a
  longer budget shows.
- Beating the references on decided counts is the floor. The lead this
  project is built for is the checked artifact behind every `unsat` and the
  counted trusted base, which S5 extends to theory reasoning; no reference
  publishes that.
