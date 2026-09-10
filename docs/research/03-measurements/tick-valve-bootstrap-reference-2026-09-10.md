# The tick valve's bootstrap constant is out of its window, and it is also unrouted — the shipping gate is a different gate, and that one cannot refuse

**Date:** 2026-09-10 · **Lane:** T1 · **Host:** `s4` (12th Gen Intel i5-12600K,
6 P-cores / 4 E-cores, 16 threads, 123 GB) · **Corpus:** the pinned
`bench-results/parity-lists/QF_BV.txt` (200 files, sha256
`6f873e15b19160eca0f006a233f5341928028a76ba04b5a1e65ff0a1a9451d4a`).

## Summary

Roadmap item 3.2's measurement note
([`remaining-inprocessing-passes-2026-09-10.md`](remaining-inprocessing-passes-2026-09-10.md))
ends with a named next task: `TickEffort::bootstrap_reference` is `2_000_000`,
the useful window is `[3_375_600, 64_294_400)`, so move it. This lane was sent
to do that.

Two findings, in the order they change the task:

1. **The window re-derives exactly.** Every number in the 3.2 note's §2, §3b,
   §4 and §5 reproduces from the committed rows — window bounds to the unit,
   98/195, 99.8%, 2,537,430, 0.68%, 12 ruinous files. §1 below.
2. **`TickValve` is not on the shipping path, and nothing else reads
   `bootstrap_reference` either.** The solver's inprocessing call site has its
   own admission policy, written against `axeyum_ir::budget` rather than
   `axeyum_cnf::ticks`. So the constant the 3.2 note identifies as "the real
   lever" is dead configuration with respect to every verdict this solver
   produces. §2.
3. **The gate that *is* routed cannot refuse.** Its refusal condition is
   arithmetically unreachable on this corpus: it requires fewer than **45.3 ms**
   of remaining budget on the largest file in the list, and less on all 194
   others, at a call site that runs with ~20 s remaining. Its work budget is
   vacuous too, on 191 of 195 files. §3.

So the finding this lane was sent to act on is **correct about the constant and
wrong about the lever**. The recommendation and the measured before/after are in
§4 and §5.

---

## 1. Re-deriving the window (nothing inherited)

The 3.2 note's §3b/§4 are a re-analysis of committed rows, so this lane
re-implemented the analysis from the schema rather than re-running the sweep,
and did not read the note's arithmetic while writing it. Source:
`bench-results/inprocess-cost-2026-09-08/qfbv-24s-{off,vivify}.jsonl` (200 rows
each).

The admission rule, read from `crates/axeyum-cnf/src/ticks.rs:543-576`:

```
reference = if search_ticks - watermark == 0 { bootstrap_reference } else { accrued }
allowance = reference * per_mille / 1000
threshold = threshold_per_clause * clauses
refuse iff allowance < threshold          # watermark NOT advanced on refusal
```

with `MAJOR_PASS` = 100‰ / 5x for subsumption, `EXPENSIVE_SETUP` = 50‰ / 20x for
BVE, and one pre-search round so `search_ticks == 0` always.

```
files in vivify arm: 200; ran inprocessing: 195

== stage totals (ms) ==
  xor_propagate_ms            108.5    0.04%
  subsume_ms                59019.4   21.50%
  vivify_ms                  2522.4    0.92%
  bve_ms                   209666.4   76.39%
  compact_ms                 2168.6    0.79%
  inprocess_ms             274454.2  100.00%

== valve at shipping bootstrap_reference = 2,000,000 ==
  subsume allowance 200,000  bve allowance 100,000
  subsume refused 58/195  spend refused 57936 ms (98.2% of subsume spend)
  bve     refused 98/195  spend refused 209207 ms (99.8% of bve spend)
  bve_variables_eliminated: total 2,537,430, on valve-admitted files 17,162 (0.68%)

== window ==
  gain file simple_processors_008_006_0004.smt2
    clauses pre-subsume 8,510 post-subsume 8,439
    -> BVE allowance must be >= 168,780  => bootstrap >= 3,375,600
  files with bve_deadline_expired: 12  carrying 96728 ms of 209666 ms
    smallest ruinous threshold 3,214,720 (bench_3010.smt2)
    -> BVE allowance must be < 3,214,720  => bootstrap < 64,294,400
  WINDOW = [3,375,600, 64,294,400)   shipping 2,000,000 is 1.69x below the floor

== frontier ==
  off decides 186/200; undecided 14
  vivify decides 188/200; converts 2 of off's undecided
  of off's undecided, 5 never reach a CNF
    CONVERTED: simple_processors_008_006_0004.smt2
    CONVERTED: bench_3388.smt2
```

**Verdict on step 1: the 3.2 note reproduces to the unit.** No disagreement to
report. The one refinement: the upper bound is correctly *exclusive*, because
the rule refuses on `allowance < threshold`, so at exactly `64,294,400` the
smallest ruinous file is admitted (equality admits). The sweep table confirms
it — `ruin adm` goes 0/12 → 1/12 at that value and not one step later.

Sweep, recomputed:

| `bootstrap_reference` | BVE allowance | BVE admitted | BVE ms kept | ruinous admitted | gain admitted | subsume admitted | subsume ms kept |
|---:|---:|---:|---:|---:|---:|---:|---:|
| **2,000,000** (shipping) | 100,000 | 97/195 | 459 | 0/12 | **no** | 137/195 | 1,083 |
| 3,375,600 (floor) | 168,780 | 117/195 | 1,196 | 0/12 | YES | 151/195 | 2,534 |
| 5,000,000 | 250,000 | 125/195 | 2,375 | 0/12 | YES | 157/195 | 3,849 |
| 10,000,000 | 500,000 | 134/195 | 9,415 | 0/12 | YES | 176/195 | 11,031 |
| 20,000,000 | 1,000,000 | 148/195 | 25,552 | 0/12 | YES | 182/195 | 15,090 |
| 40,000,000 | 2,000,000 | 160/195 | 55,506 | 0/12 | YES | 187/195 | 22,197 |
| 64,294,400 (ceiling) | 3,214,720 | 169/195 | 92,154 | **1**/12 | YES | 191/195 | 34,946 |
| 200,000,000 | 10,000,000 | 184/195 | 133,943 | **2**/12 | YES | 195/195 | 59,019 |

Reproduce: the script is quoted in §7.

---

## 2. `TickValve` is routed nowhere the solver can reach

`grep -rn 'TickValve\|TickEffort\|bootstrap_reference' --include='*.rs' crates/`
returns hits in exactly three places:

* `crates/axeyum-cnf/src/ticks.rs` — the definition.
* `crates/axeyum-cnf/src/inprocess.rs` — `TickValve<O>`, its
  `InprocessObserver` impl, and `DECOMPOSE_EFFORT`.
* `crates/axeyum-cnf/tests/{inprocess_tick_valve,decompose_substitution}.rs` —
  the tests.

**Zero hits in `crates/axeyum-solver`.** The 3.2 note anticipated the second
half of this (it lists "route `TickValve::shipping` around
`BackendInprocessObserver`" as step 2 of its recommendation, and separately
records that `decompose_grant` is the defaulted `None`), but it filed the
routing as a follow-up to the constant. The order is the other way round: the
constant is *inert until* the routing happens, so "move the constant and
re-measure 1.2" cannot produce a non-null result on its own.

What is actually routed, at `crates/axeyum-solver/src/sat_bv_backend.rs:294`
→ `inprocess()` → `BackendInprocessObserver`:

```rust
impl InprocessObserver for BackendInprocessObserver<'_> {
    fn grant(&mut self, pass: OccurrencePass, formula: &CnfFormula) -> Option<u64> {
        match pass {
            OccurrencePass::Subsume => subsume_admission(formula, self.deadline, self.stats),
            OccurrencePass::Bve => bve_admission(formula, self.deadline, self.stats),
        }
    }
    // `decompose_grant` not overridden -> the defaulted `None`
}
```

Both route to `admit_occurrence_pass`
(`sat_bv_backend.rs:1499-1565`), which builds an
`axeyum_ir::budget::EffortPolicy` — a *second, independent* implementation of
the same CaDiCaL accumulate-and-delay idea that `axeyum_cnf::ticks` implements.
The tree carries both. Only one of them decides anything.

The two differ in the quantity they call a reference window, and this is the
part worth carrying forward:

| | `axeyum_cnf::ticks::TickValveAccount` (unrouted) | `admit_occurrence_pass` (shipping) |
|---|---|---|
| pre-search reference | fixed constant `bootstrap_reference` | `min(setup x B, remaining_ms x steps_per_ms)` |
| threshold | `threshold_per_clause x clauses` | `min_recovery_multiple x setup` |
| `setup` | not used | `literal_occurrences + 2 x variable_count` (exact, the meter's own start value) |

The shipping reference is **formula-relative**; the unrouted one is a fixed
integer. That is why the fixed integer "crossed a unit boundary without
recalibration", as the 3.2 note puts it — and it is also an argument that
routing the fixed-constant valve in place of the formula-relative one would be a
step down, not up. §4.

---

## 3. The routed gate cannot refuse, and its budget is vacuous on 191/195

`admit_occurrence_pass` refuses iff `reference < min_recovery_multiple x setup`,
i.e.

```
min(setup x B, remaining_ms x SPS)  <  R x setup
```

with the shipping constants `B = BVE_BUDGET_SETUP_MULTIPLE = 2_000`,
`R = BVE_MIN_RECOVERY_MULTIPLE = 2`, `SPS = BVE_STEPS_PER_MILLISECOND = 400_000`.

**The size arm can never trip it.** `setup x B < R x setup` iff `B < R`, and
`B = 2000`, `R = 2`. So refusal requires the *wall* arm to be the minimum
*and* below `R x setup`:

```
remaining_ms  <  R x setup / SPS  =  setup / 200_000
```

Per file, measured over the 195 that ran inprocessing (setup reconstructed as
`inprocess_literals_before + 2 x cnf_variables`):

```
wall arm refuses iff remaining_ms < R*setup/SPS; per file that bound is:
  div3.c.50.smt2                    setup= 9,050,520  needs remaining_ms < 45.253 ms
  148.smt2                          setup= 5,214,449  needs remaining_ms < 26.072 ms
  bin_eventlogadm_vc352379.smt2     setup= 4,844,507  needs remaining_ms < 24.223 ms
  convert-jpg2gif-query-1166.smt2   setup= 4,823,859  needs remaining_ms < 24.119 ms
  bin_libmsrpc_vc1225899.smt2       setup= 3,197,552  needs remaining_ms < 15.988 ms
  across all 195 files the refusal thresholds run 0.0000 .. 45.253 ms
```

The call site runs before the search with ~20 s of a 24 s budget left. **The
gate refuses on 0 of 195 files, and the largest file in the corpus would need
the budget to be 99.8% exhausted before it did.**

Its work budget is nearly as inert. `setup x B` binds on **191 of 195** files
(the wall arm on 4), and on the 12 files that record `bve_deadline_expired` the
granted budget is between 1.06 G and 18.1 G steps against a pass that the wall
clock cut off after 0.3–11.5 s:

| file | setup | size arm (`setup x 2000`) | wall arm @20 s | arm that bound | `bve_ms` | implied steps/ms |
|---|---:|---:|---:|:--|---:|---:|
| `bench_3010` | 531,246 | 1,062,492,000 | 8,000,000,000 | size | 11,513 | 92,284 |
| `bin_libsmbsharemodes_vc5714` | 1,097,366 | 2,194,732,000 | 8,000,000,000 | size | 10,793 | 203,356 |
| `bin_libsmbsharemodes_vc6315` | 1,763,782 | 3,527,564,000 | 8,000,000,000 | size | 9,742 | 362,089 |
| `bin_eventlogadm_vc331099` | 1,994,653 | 3,989,306,000 | 8,000,000,000 | size | 9,662 | 412,887 |
| `bench_12354` | 2,868,285 | 5,736,570,000 | 8,000,000,000 | size | 8,790 | 652,643 |
| `bin_libsmbclient_vc1225764` | 2,801,924 | 5,603,848,000 | 8,000,000,000 | size | 8,639 | 648,646 |
| `148` | 5,214,449 | 10,428,898,000 | 8,000,000,000 | wall | 8,326 | 960,887 |
| `bin_libmsrpc_vc1225899` | 3,197,552 | 6,395,104,000 | 8,000,000,000 | size | 8,188 | 780,987 |
| `tsp_rand_70_300_...` | 3,162,854 | 6,325,708,000 | 8,000,000,000 | size | 8,012 | 789,533 |
| `bin_eventlogadm_vc352379` | 4,844,507 | 9,689,014,000 | 8,000,000,000 | wall | 6,973 | 1,147,216 |
| `convert-jpg2gif-query-1166` | 4,823,859 | 9,647,718,000 | 8,000,000,000 | wall | 5,769 | 1,386,624 |
| `div3.c.50` | 9,050,520 | 18,101,040,000 | 8,000,000,000 | wall | 320 | 24,984,526 |

The "implied steps/ms" column is the granted budget divided by the milliseconds
the pass actually ran; it is an upper bound on throughput, not a measurement of
it, and it is 0.2x–62x `BVE_STEPS_PER_MILLISECOND`. What it does establish is
that on every one of these files the pass stopped because the **wall deadline**
arrived, not because it spent its work budget. The gate's own registry entry
(`config_registry.rs`, `BVE_MIN_RECOVERY_MULTIPLE`) says it "arms the
accumulate-and-delay gate ... do not start a pass whose fixed setup cost the
available budget cannot recover twice over". That is true of the code and
vacuous on the corpus.

This is the CLAUDE.md shape verbatim: *a checker that cannot fail is worse than
no checker*. Item 1.2's 274 s of inprocessing spend is not the tick valve
refusing too much; it is a gate that has never refused anything, handing out a
budget three orders of magnitude larger than the pass can consume, with the wall
clock as the only real bound.

---

## 4. Recommendation

**DO NOT move `TickEffort::bootstrap_reference` as a performance change, and do
not route `TickValve` into the solver.** Three reasons, in order of weight:

1. **Moving it changes no outcome, because nothing on the solve path reads it**
   (§2, and the mutation control in §5). A before/after table over the corpus
   for that change would be a table of zeroes, and publishing one would be
   worse than not measuring: it reads as "the lever does not work" when the
   truth is "the lever is not connected".
2. **Routing it would replace a formula-relative reference with a fixed
   integer** (§2's table). The shipping gate's window scales with
   `literal_occurrences + 2 x variable_count`; `bootstrap_reference` does not
   scale with anything. The 3.2 note's own §4 caveat — "this is a fit with
   n = 1 on the positive side" — is a fit of one constant to one file, and the
   quantity it is fitting is the one the shipping design already made
   size-relative on purpose.
3. **The window is not the binding constraint anyway.** The 3.2 note's window
   is derived to make BVE *refuse* on the 12 ruinous files. The shipping gate
   already has a knob that bounds those files without refusing them —
   `BVE_BUDGET_SETUP_MULTIPLE`, which is granting 1.06–18.1 G steps to passes
   the clock stops at under 12 s (§3). Bounding is strictly better than
   refusing here: a bounded BVE still delivers the reductions it finds early,
   and a refused BVE delivers none.

**What to do instead, and it needs no new code:** arm the gate that ships.
`BVE_BUDGET_SETUP_MULTIPLE` already carries an environment override
(`AXEYUM_BVE_BUDGET_MULTIPLE`), so the whole sweep is one binary. §5 measures it.

The one change to `ticks.rs` that *is* warranted is documentation, not a value:
the constant should say that it is not read on any shipping path, so the next
lane does not spend a session on it. See §6.

---

## 5. Before/after

### 5a. The constant: a null, with a positive control that fires

The static argument in §2 is a grep, so it was checked by mutation. Two release
binaries were built from this tree and run over the **same 60 fixtures**:

* **shipped** — `bootstrap_reference = 2_000_000`, valve unrouted (today's tree).
* **boot0** — `bootstrap_reference = 0`, valve unrouted. Zero rather than
  10,000,000 deliberately: it is the most discriminating value there is, because
  a live constant at zero makes `allowance` zero and refuses *every* pass. If the
  constant were read at all, this could not be invisible.

The fixtures are the 60 fastest parity-list files on which BVE eliminated
variables and **no pass hit its deadline**, so every counter compared is
deterministic and a difference could not be blamed on timing. Verified in the
run itself: `deadline expiries across BOTH arms: 0`.

```
fixtures: 60
shipped-arm totals (the population must be non-vacuous):
   bve_variables_eliminated                   47,458
   bve_clauses_removed                       183,294
   bve_clauses_added                          72,167
   subsume_clauses_subsumed                   43,886
   subsume_literals_strengthened              39,946
   vivify_clauses_strengthened                84,196
   cnf_compaction_variables_dropped           50,106
   inprocess_literals_before                 712,608
   inprocess_literals_after                  299,213

deadline expiries across BOTH arms: 0 (must be 0 for determinism)

verdict differences: 0
deterministic-counter differences: 0
```

**Zero differences.** Moving the constant — to the most extreme value in its
domain — changes nothing the solver does.

A null is worth nothing without a control that the harness can detect a live
constant, so the identical comparison was run over the identical 60 fixtures
with two binaries in which the valve **is** routed (§5b's patch),
`bootstrap_reference` 2,000,000 vs 10,000,000 — a *smaller* change than the
negative arm's:

```
verdict differences: 0
deterministic-counter differences: 255
```

Same fixtures, same counters, same comparison, a smaller change to the same
integer: **255 differences when routed, 0 when not.** The harness sees a live
constant. It does not see this one.

### 5b. The corpus, four arms, one binary

Full pinned 200-file QF_BV parity list, 24,000 ms budget, each arm pinned to a
**distinct physical P-core** (0/2/4/6) and run concurrently, `measured=200
rows=200` on every arm. `off` is the no-inprocessing baseline; `base` is today's
shipping configuration; `bve500`/`bve100` lower
`BVE_BUDGET_SETUP_MULTIPLE` from 2,000 through the existing
`AXEYUM_BVE_BUDGET_MULTIPLE` lever — the same binary, so no build difference has
to be argued away.

Host `s4`; 1-minute load `15.52` at start, `19.14`–`24.59` at the arms' ends.
**The box was busy** and two release builds overlapped the run; see the caveat
below.

| arm | decided | sat | unsat | unknown | wall (s) | inprocess (s) | bve (s) | subsume (s) | `bve_deadline_expired` |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `off` | **185** | 56 | 129 | 15 | 574.6 | 0.0 | 0.0 | 0.0 | 0 |
| `base` (shipping) | **185** | 56 | 129 | 15 | 624.1 | 63.0 | 45.0 | 9.4 | 0 |
| `bve500` | **185** | 56 | 129 | 15 | 588.9 | 67.7 | 37.8 | 20.4 | 1 |
| `bve100` | **185** | 56 | 129 | 15 | 603.0 | 35.8 | 15.5 | 11.9 | 0 |

* **Decided count is 185 on every arm, and the decided *sets* are identical** —
  0 gained, 0 lost, pairwise, in every direction. Not one file's verdict moves.
* **0 sat/unsat disagreements** across all four arms. Nothing became wrong.
* Inprocessing spend moves by 1.9x between arms (35.8 s to 67.7 s) and buys no
  verdict either way.

**Wall clock does not resolve at this load, and the honest reading is that it
says nothing.** The ordering is not monotone in the lever: `bve100` grants BVE
the *smallest* budget, does the *least* inprocessing (35.8 s), and finishes
*slower* (603.0 s) than `bve500` (67.7 s of inprocessing, 588.9 s). A lever whose
tightest setting is slower than its looser one is being read through contention,
not through the solver. Nothing about wall clock is claimed from this run.

**Two caveats on comparability, stated because they bound what this table
supports.** Each arm was pinned to ONE logical CPU (the committed 2026-09-08
sweep used six), and the box carried other lanes plus two of this lane's own
release builds. Absolute figures therefore do not match the committed run —
`off` decides 185 here against 186 there, and `base` records 45.0 s of BVE and
**0** `bve_deadline_expired` against 209.7 s and 12. The arms are internally
comparable to each other because they shared conditions; they are **not**
comparable to the 2026-09-08 rows, and §1's window is derived from those rows,
not from these.

### 5c. Routing the valve, measured rather than argued

<!-- T1: the three-arm phase-2 sweep (base2 / valve2M / valve10M) was still
     running when this section was committed. Filled in below when it lands;
     "pending" here means it did not run, not that it agreed. -->

---

## 6. What changed in the tree

<!-- T1: pending -->

---

## 7. Reproducing

```sh
# Section 1 and 3 are pure re-analysis of committed rows -- no build:
#   bench-results/inprocess-cost-2026-09-08/qfbv-24s-{off,vivify}.jsonl
# valve decision:  allowance = bootstrap_reference * per_mille / 1000
#                  threshold = threshold_per_clause * clauses
#                  refuse iff allowance < threshold
# BVE's clause count is post-subsume:
#   cnf_clauses - subsume_clauses_subsumed - subsume_tautologies_removed
# shipping gate:   reference = min(setup * B, remaining_ms * SPS)
#                  threshold = R * setup
#                  setup     = inprocess_literals_before + 2 * cnf_variables
#
# Section 2 is a grep, and its negative is the finding:
grep -rn 'TickValve\|TickEffort\|bootstrap_reference' --include='*.rs' crates/axeyum-solver/
#   -> no output. Positive control on the same pattern:
grep -rln 'TickValve' --include='*.rs' crates/
#   -> crates/axeyum-cnf/{src/inprocess.rs,tests/*.rs} only.
```
