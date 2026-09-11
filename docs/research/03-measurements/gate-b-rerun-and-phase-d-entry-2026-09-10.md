# Gate (b) re-run on a quiet box, and whether Phase D's entry condition is met

**Lane `E8-core-position`. Date: 2026-09-10/11. Host: `s4` (12th Gen Intel
i5-12600K, 6 P-cores / 4 E-cores, 16 threads, 123 GB). Tree: `1a03d7e91`.**

Subject: **Phase D** of
[the CDCL consolidation plan](../../solver-comparison-2026-09/12-cdcl-consolidation-plan.md),
which is gated on a condition rather than a date:

> *Entry condition, not a date:* Phase C has closed and a conflict-count
> comparison still shows a material gap on a family we care about.

Phase C closed on 2026-09-10
([note](theory-interface-completeness-2026-09-10.md)). This note settles the
second conjunct. The decision is
[ADR-1914](../09-decisions/adr-1914-phase-ds-entry-condition-is-not-met-and-the-core-gap-is-mid-budget-not-structural.md);
the artifact is [`bench-results/sat-core-gate-b-20260910/`](../../../bench-results/sat-core-gate-b-20260910/).

Every number below was produced by a command run in this lane's worktree.
Where a check did not run, it says "did not run" rather than being inferred.

## 0. Answer

**Not met.** The gap is real, small, and — the part that decides it — **almost
entirely mid-budget rather than structural**. Across both families the
references decide exactly **two** files with 4x headroom or more that the
native core misses, and on one of those two the two references disagree with
each other by 18x, which makes it an artefact of where a search fell rather
than a technique we lack.

Phase D **closes unentered**, with a re-entry condition stated in §6.

## 1. The condition has two readings and both were checked

"A conflict-count comparison on a family we care about" can mean the
theory-side instrument Phase C built, or the pure-CNF engine comparison that
gate (b) is. Different families, different engines, so both.

### 1.1 Theory side — swept, and the one family it flagged was already priced

Phase C ran `route_solo --stats` against `z3 -st` over the 120 files in
`bench-results/parity-losses-20260908/`
([§4 of the Phase C note](theory-interface-completeness-2026-09-10.md)):

| division | conflict ratio vs z3 | bearing on Phase D |
|---|---|---|
| QF_LRA | n/a — the search barely runs | losses are encoder-admission and model-replay |
| QF_LIA | n/a — same | one file spent its whole 20 s in a single `theory_assert` |
| QF_UFLIA | 1.5x – 1.8x | close; the loss is upstream of the route |
| QF_IDL | 2.3x – 39.7x | **the one real family — fix measured and REJECTED** |
| QF_SLIA | **did not run** | see §5 |

QF_IDL is the case that matters, because it is the only cell where the
instrument said *yes* and the answer was carried through to a verdict count.
Lifting `MAX_PROPAGATION_VERTICES` cut conflicts **1.5–8.1x** and took the
division from **8 of 9 decided to 6 of 9**. The conflicts went the right way
and the product went the wrong way. That is Phase C's own correction — *a
ratio is a diagnosis of cause, not a prediction of value* — and it is the
reason this note refuses to price any technique by conflicts.

Three cells are open and named as open (§5). None of them currently *shows* a
gap, so none of them meets the entry condition; what they do is bound how far
this answer generalises.

### 1.2 Pure-CNF side — that is gate (b), and it had never been re-run quiet

[ADR-1703](../09-decisions/adr-1703-the-native-core-is-the-sat-engine-batsat-is-demoted-to-a-differential-oracle.md)
rests on a 2026-09-05 four-engine sweep whose own caveat is that the host
"was heavily loaded by unrelated lanes throughout" (`load average` 12–33,
one spike to 111), so *ordering* was reliable and absolute seconds were not.
That is the measurement this note re-runs.

## 2. Method

Deliberately the same shape as 2026-09-05, so the two tables are comparable.

1. **Corpora and DIMACS.** `crates/axeyum-bench/examples/dump_dimacs.rs`
   (unmodified) over the same two families, with the same seeded 100-file
   Noetzli sample. **213 of 213 dumped, 0 failures.**
2. **Control on the inputs.** Variable and clause counts match the 2026-09-05
   dumps on **212 of 213** files, so the two runs are on the same formulas.
   The exception is `bv-term-small-rw_388`, which the word-level preprocessing
   has since shrunk from 3,533 variables / 14,999 clauses to **213 / 665**.
3. **Three engines, identical DIMACS, 20 s per instance, `taskset -c 0-7`, one
   engine at a time.** Native is `solve_with_drat_proof_within` through
   `gate_b_sweep sweep`; CaDiCaL 3.0.1 and Kissat 4.0.4 are external binaries
   through `external_sweep.py` (committed here; the 2026-09-05 equivalent
   lived in that lane's scratchpad and was never committed).
4. **Every `sat` verdict model-checked** by `CnfFormula::evaluate` — the native
   arm inside `gate_b_sweep sweep`, the external arms through
   `gate_b_sweep verify`. The same trusted code path in every case.
5. **A quiet box.** `uptime` before and after each of the six engine/family
   pairs: load average **1.01–1.16** throughout, against 12–33 in 2026-09-05.
   Nothing else ran; `ps` showed one solver at 100% of one core.

## 3. The table

| Engine | p4dfa / 113 | 2026-09-05 | PAR-2 (s) | Noetzli / 100 | 2026-09-05 | PAR-2 (s) |
|---|---:|---:|---:|---:|---:|---:|
| native | **9** | 6 | 37.248 | **87** | 86 | 5.203 |
| CaDiCaL 3.0.1 | **12** | 10 | 36.339 | **89** | 88 | 4.646 |
| Kissat 4.0.4 | **14** | 11 | 35.873 | **90** | 89 | 4.116 |

**Zero cross-engine verdict disagreements** over 639 (engine, file) pairs.
Every `sat` model valid, 54 of 54.

**Every engine gained on a quiet box**, and that is the first thing the re-run
had to establish: the 2026-09-05 figures were depressed by contention on all
columns, not only ours. The improvement is therefore not all ours to claim.
Net movement: the gap to CaDiCaL on p4dfa narrows from 4 files to 3; the gap
to Kissat is 5 files in both runs.

PAR-2 separates the engines by **0.91 s (CaDiCaL) and 1.38 s (Kissat)** out of
a 40 s two-timeout ceiling on p4dfa — 2.3% and 3.7% — and by 0.56 s / 1.09 s
on Noetzli.

## 4. Is the gap material? The boundary decomposition

A decided-count is a threshold statistic: it says nothing about *how far* past
the threshold a win was. "The reference decides it in 0.2 s of a 20 s budget"
and "in 19 s of a 20 s budget" are different claims about what a core
improvement would have to buy. So every file a reference decides and the
native core does not is bucketed by the reference's own wall time.

| | far (≤ 5 s, ≥ 4x headroom) | mid (5–15 s) | near (> 15 s) |
|---|---:|---:|---:|
| p4dfa, CaDiCaL's 3 extra | **0** | 3 | 0 |
| p4dfa, Kissat's 6 extra | **0** | 4 | 2 |
| Noetzli, CaDiCaL's 2 extra | **0** | 2 | 0 |
| Noetzli, Kissat's 3 extra | **2** | 1 | 0 |

**Two files in 213.** That is the whole population of instances a reference
cracks with real headroom and we do not: `bv-term-small-rw_524` (Kissat
0.60 s) and `bv-term-small-rw_848` (Kissat 0.78 s).

**And one of the two refutes its own reading.** On `bv-term-small-rw_524`,
Kissat takes 0.60 s and **CaDiCaL takes 11.05 s** — an 18x spread between the
two *references*. A gap that large between two mature solvers on one instance
is not a technique the loser is missing; it is which way a search fell. A
single file's ratio cannot carry a technique argument, and this file is the
counterexample that proves it.

The relation is also not containment: the native core decides
`compose.p3._bit8_na6_nr3_paired` at 798.6 ms, which **Kissat does not decide
at all** inside 20 s.

### 4.1 How far off is the core on the files it misses?

The bucket above prices the *reference's* effort. This prices ours: re-run the
native core on exactly the files a reference decides and it does not, at 5x and
15x the gate budget. A file it decides at 100 s is a **speed** gap of known
size; one it does not decide at 300 s is a different kind of problem.

p4dfa, the 6 files a reference decides and the native core does not at 20 s:

| file | native at 100 s | best reference | factor |
|---|---|---:|---:|
| `string1x8.3` | **sat, 23.1 s** | Kissat 5.6 s | 4.2x |
| `videoconf_simple` | **sat, 44.4 s** | Kissat 5.2 s | 8.5x |
| `string1x8.6` | **sat, 50.2 s** | Kissat 7.4 s | 6.8x |
| `string1x8.1` | **sat, 80.1 s** | Kissat 17.6 s | 4.6x |
| `string1x8.4` | unknown at 300 s (timed out) | Kissat 8.3 s | **> 36x** |
| `tcp_open` | unknown at 300 s (timed out) | Kissat 18.2 s | **> 16x** |

**Four of the six are a 4–9x speed gap. Two are beyond a 15x budget.** That is
the honest shape of the p4dfa deficit: mostly tuning-scale, with a residue of
two files that are not.

The 300 s arm reproduces the 100 s wall times to within 1% on all four decided
files (80.11 → 80.67, 23.14 → 23.29, 50.16 → 49.99, 44.42 → 44.43 s), which is
a determinism control on the measurement itself.

### 4.2 One reading here is NOT a timeout, and it looks exactly like one

On the three Noetzli files a reference decides and we do not:

| file | native at 300 s | `timed_out` | best reference |
|---|---|---|---:|
| `bv-term-small-rw_1074` | **unsat, 118.9 s** | false | Kissat 9.3 s |
| `bv-term-small-rw_524` | unknown, **194.7 s** | **false** | Kissat 0.60 s |
| `bv-term-small-rw_848` | unknown, **243.6 s** | **false** | Kissat 0.78 s |

The last two stop at 194.7 s and 243.6 s *inside a 300 s budget* with
`timed_out = false`. They did not run out of time. They returned
`ProofSolveOutcome::ResourceOut` — the search hit
`DEFAULT_PROOF_SAT_CONFLICT_LIMIT = 2_000_000`
(`crates/axeyum-cnf/src/proof_sat.rs:50`) and gave up on its own.

So "unknown at 300 s" on those two rows means **"> 2,000,000 conflicts"**, not
"> 300 s", and their true time-to-decide is unmeasured. Recorded because the
two readings are indistinguishable in the verdict column and one of them would
have overstated the gap.

**The cap does not explain the gate result.** At the 20 s budget every
undecided native result on both families — 104 of 113 on p4dfa, 13 of 100 on
Noetzli, 117 in total — carries `timed_out = true`. The conflict cap is
reached on **zero** of them. It becomes the binding constraint only above
roughly 195 s, which is 10x the budget gate (b) measures at.

### 4.3 On the files both engines decide, the relation is mixed

A decided-count is a threshold statistic and says nothing about either side of
the threshold. On the p4dfa files both engines decide:

| | native faster | native slower | median ratio |
|---|---:|---:|---:|
| vs CaDiCaL (9 files) | 6 | 3 | **0.86x** |
| vs Kissat (8 files) | 5 | 3 | **0.79x** |

The three the native core loses are the interesting ones, and only one is
large: `mobiledevice_bit8_na6_nr3_paired` at **8.98x** CaDiCaL and 6.41x
Kissat. The other two are 2.1–2.7x. Against that, it is **30x faster** than
Kissat on `compose.p2` and 5.3x faster than CaDiCaL on `compose.p3`.

*The parse bias is measured, not assumed.* Kissat's own profiler reports
`parse` at **0.04 s, 1.31% of a 3.02 s run** on the 7.2 MB `compose.s2`
DIMACS. So the native arm's excluded parse time is under 2% of any
second-scale row above and cannot account for these ratios; on the
sub-second rows it is a larger share (roughly 10%) and those ratios should be
read loosely.


## 5. What this does not establish

- **QF_SLIA did not run, and closing it is not the one-entry change the Phase
  C note says it is.** That note proposes adding the string route to
  `route_solo`'s table. `route_solo`'s `Route.run` signature is
  `fn(&mut TermArena, &[TermId], &SolverConfig)` — it receives
  `script.assertions`. The online string route the front door actually runs
  consumes `Script::word_skeleton`, a **separate** parallel `Seq`-level view
  (`crates/axeyum-smtlib/src/parse.rs:244`) that is populated all-or-nothing
  and is **empty whenever any atom uses `str.len`, `substr`, regex or an
  extended function**. A naive route entry would therefore measure the
  raw-assertion decline, not the route — an empty result indistinguishable
  from a strong negative. A cheap census would settle it without
  building a vacuous instrument: `crates/axeyum-smtlib/examples/proof_gap_shape_census.rs`
  already prints `word_skeleton_terms` per file (`:120`). **That census did not
  run in this lane.**
- **Two further Phase C cells are open**: `ufbv_online` on QF_UFBV and
  `combined_theory` on QF_UFLRA. Neither shows a gap; neither has been looked
  at.
- **The improvement since 2026-09-05 is not attributed.** 34 commits have
  touched `crates/axeyum-cnf/src/proof_sat.rs` since that run — the three-tier
  clause database, the binary-clause watch fast path, the reduce schedule
  among them — and nothing here isolates which moved the count.
- **One bias runs in our favour and is not corrected.** The native arm starts
  its clock after parsing the DIMACS; an external binary pays parse inside its
  budget. Every reference advantage above is therefore a **lower** bound.
  Measured at **1.31%** of a
  3.02 s Kissat run on a 7.2 MB DIMACS (§4.3), so it is small, but it is
  present and it is never in the references' favour.
- **This is pure-CNF only.** It says nothing about `CdclT` or about the
  CDCL(T) routes, exactly as gate (b) did not.

## 6. Re-entry condition

Phase D reopens if any one of these becomes true, and not otherwise:

1. A reference decides **three or more** files in one family with ≥ 4x budget
   headroom that the native core misses, on a quiet box, with both references
   agreeing within 4x on each such file (so a single lucky trajectory cannot
   trigger it).
2. One of the three open Phase C cells (§5) is measured and shows a
   conflict-count gap whose closure is then shown to **decide more files**,
   not merely fewer conflicts.
3. The PAR-2 separation on a family we care about exceeds 10% of the
   two-timeout ceiling. It is 2.3–3.7% today.
