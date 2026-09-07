# Lane: s7b-engine-unification — the same instrument on both engines, then the first route moves

<!-- plan-section: lane-status -->

**S7b landed three of its four steps. The native CDCL(T) core carries `CdclT`'s
driver-side instrument; a `TheorySolver` can drive it through
`native_cdclt::NativeTheoryAdapter`; and the difference-logic route runs on it —
so a `QF_IDL`/`QF_RDL` refutation now reaches the front door with an ADR-1704
trust step instead of an empty ledger, and the QF_IDL timeout population goes
27/50 → 31/50 decided at PAR-2 −12.9% with zero verdict changes. The engine
differential found two real defects before any of it shipped, one of them a
wrong-`unsat` shape** (`WIP`, s7b-engine-unification, 2026-09-07, plan slice
S7b).

S7a ([`s7-engine-unification.md`](s7-engine-unification.md)) made the native
core decide under a theory and produce the ADR-1704 artifact; nothing reached
it. This lane is the part that changes what the arithmetic routes run.

## Two corrections to S7a's scoping, both load-bearing

1. **The adapter cannot be a blanket impl.** `impl<T: TheorySolver>
   NativeTheory for T` is rejected by the orphan rule — `NativeTheory` is
   foreign to `axeyum-solver` and the impl covers foreign types. It is a local
   newtype.
2. **The incremental refinement protocol has ONE client, not ten.** S7a listed
   `with_inactive_variables` / `add_theory_variable` / `add_permanent_clause` /
   a resumed solve as the blocker. Only **`ufbv_online`** uses any of it.
   `dl_online`, `lra_theory`, `lia_theory`, `euf_egraph`, `string_theory`,
   `uflra_online` and `uflia_online` are all `CdclT::new` followed by exactly
   one `solve`. So the one-shot half of the protocol unblocks seven routes, and
   step 3 of S7a's plan (dormant variables, permanent clauses) is not a
   prerequisite for any of them.

## Step 1 — the instrument, validated before anything moved

### The `CdclT` side reproduces S1b's numbers

Idle s5, `taskset -c 0-7`, 24 s, `smtcomp_cli --trace`, binary from a
`--touch`-extracted snapshot of `fcc988900`. `RVpredict_13`, the file S1b
pinned:

| | S1b recorded (`9a0615cfe`) | here (`fcc988900`) |
|---|---:|---:|
| verdict | `sat` | `sat` |
| `decisions` | 2,364,618 | **2,364,618** |
| `theory_conflicts` | 3,415 | **3,415** |
| `restarts` | 17 | **17** |

Exact on all four across the S2, S4 and S7a merges in between. The instrument is
sound and the before-numbers reproduce, which is what this slice was gated on.

One thing has moved since S1: **all five profiled files now emit a trace line.**
S1 reported three of five printing none (its Finding 0, the watchdog dying
inside routing); S2's shared shrinking deadline closed that. The two `asp` files
it unblocked are where Boolean propagation dominates again (15,488 ms and
16,642 ms of ~22 s).

### The native side carries the same counters

`axeyum_cnf::NativeLayerStats`: the fifteen driver-side fields of
`axeyum_solver::layers::TheoryLayerStats`, at the same increment sites, with
`restarts` derived as `restart_count - 1` exactly as `CdclT::restarts` derives
it. Theory-side engine counters are deliberately not ported — they belong to the
`TheorySolver`, not the driver.

Collection is opt-in. With it off, no stage reads a clock and no counter is
touched, so an unmeasured run is all-zero rather than a partial measurement.

**The shipping SAT trajectory is byte-identical**: `drat_stream_dump` over the
three committed DIMACS files plus 30 seeded random 3-SAT instances emits 38,333
bytes, sha256 `84a620da…` — the digest S6 and S7a each recorded before this
change existed, so matching it is a check and not a self-comparison.

## Step 2 — the adapter, and the two defects the differential found

`native_cdclt::NativeTheoryAdapter` wraps a `TheorySolver` so the native core
can drive it, negating **once** at the boundary: `TheorySolver` carries asserted
literals, `NativeTheory` carries clauses. It owns the atom↔variable map the
native core does not keep and extends it in lockstep with dynamic registration.

The gate is a differential, not an inspection: 4,000 random CDCL(T) instances
through both engines in both the eager and the deferred explanation channel, all
8,000 runs also decided by an independent brute force over the Boolean skeleton
and the theory's semantics — so "the engines agree" cannot mean "both are wrong
the same way". The theory is hostile: non-monotone on partial assignments,
complete on total ones.

**Defect 1 — `cdclt.rs`, a panic.** `theory_propagate` wrote a lazily-propagated
literal's handle *after* assigning it, and `assign` tells the theory, which may
answer with a conflict. In that window the literal sits on the trail at the
current level with no reason clause, no reason-clause id and no handle, and
1-UIP analysis trips its own assertion. Reachable by any theory that both defers
explanations and refuses an assertion it caused — `euf_egraph` defers. Fixed by
recording the handle first.

**Defect 2 — `proof_sat.rs`, a wrong-`unsat` shape.** `NativeTheory::explain`
answers for two different objects — a conflict core, and a propagation reason,
which additionally contains the implied literal — and the
propagate-onto-an-already-false-literal path asked for a CORE where the handle
stood for a REASON. Invisible to every fixture in that file, because they all
materialise their own clauses. An adapter over an asserted-literal channel obeys
the ask, drops the implied literal, and installs `¬antecedents` as an ADR-1704
**input** clause of the extended formula — a clause the theory does not entail
(it entails `antecedents → implied`). Refuting that formula is a wrong `unsat`.
`explain` now takes the implied literal, `None` for a core and `Some(lit)` for a
reason.

On the 8,000-run population defect 2 showed up as 39 engine disagreements with
**no** wrong verdict, so on this population it manifested as a disagreement
rather than a wrong answer — but the clause it installs is not entailed, so it
is a soundness shape and not a completeness one.

### Mutation controls

Private tree on idle s5, baseline bracketing the run green both times:

| mutation | its own regression test | the differential | collateral |
|---|---|---|---|
| `deferred_reason` written after the assignment again | **killed** | **killed** | clean |
| the propagate-onto-false path asks for a CORE again | **killed** | **killed** | clean |

The first fixture **did not reproduce its defect on the first attempt**: it
forced `x0` with a unit clause, which puts the conflict at level zero where
`learn_and_backjump` returns before analysis walks anything, and it passed with
the defect reinstated. The mutation control is what caught that. The fixture now
reaches `x0` as a decision and dies as it should. Both defects were *found* by a
failing test and *fixed* against it, so the forward direction is evidence too;
the controls establish the dedicated tests carry it.

## Step 3 — the difference-logic route moves, and its unsat carries a trust step

`dl_online::try_check_qf_dl` builds the native core through
`native_cdclt::solve_native`. `evidence::dl_decided_report` attaches the trust
step the refutation now comes with.

Before this, a Boolean-structured `QF_IDL`/`QF_RDL` refutation reached
`produce_evidence` as `Evidence::Unsat(None)` with `trusted_steps` **empty** —
and the verdict rests on theory lemmas no propositional checker can see. An
empty ledger slot is indistinguishable from "nothing was assumed". Now the same
verdict carries exactly one step, `SatRefutationModuloTheory`, never certified
(ADR-1704 prohibition 2), and the count that grade branches on is
`|extended| − |cnf|`.

Two end-to-end tests, the second the control for the first:
`a_boolean_structured_difference_logic_unsat_now_carries_a_trust_step` (an
800-link chain with a disjunction, above the certifying routes' node gate,
`backend = "dl-online"`, exactly one uncertified step) and
`a_satisfiable_difference_logic_query_carries_no_trust_step` (same chain without
its closing edge: `sat`, no step — so the first is about the refutation and not
about the route stamping every report).

### Two things the swap had to carry, both found by the full sweep

**A different-but-correct model can lose a verdict.** The native core decides
FALSE first and rephases to the best assignment on restart; `CdclT` decides TRUE
first and has no rephasing. Both find correct models; they find *different*
ones, and MBQI picks its instantiation terms out of the model it is handed.
`auto::tests::mbqi_one_level_fixed_retry_is_guarded_and_replays_unfixed_seed_111_shape`
went `Sat` → `Unknown` on that alone. `TheorySolveOptions` now spells the knobs
out; defaults are the one-shot SAT defaults, and `solve_native` sets
`initial_phase: true, target_rephase: false`.

**Recording a DRAT stream is not free.** The stream is every learned clause of
the whole search held in memory, and `CdclT` — which emits no proof — never paid
it. Recording is off by default (the dispatcher wants a verdict and pays
nothing) and the evidence layer, the only consumer, turns it on for its own call
through `with_artifact_recording`; a `proof_literal_budget` (8M literals)
abandons a recording that outgrows it. Both bound the **recording** and never
the search — the sink is output-only, so the verdict and the trajectory are the
same either way and the artifact's presence can never become part of what was
decided. `TheorySolveOutcome::Unsat` therefore carries an `Option`, and the
distinction is the point: `None` is **not recorded**, `Some(artifact)` with
`theory_lemma_count() == 0` is **nothing was assumed**.

## Measured

### The micro-benchmark: the gap S7 set out to close is already closed

Same host, same session, back to back, criterion 100 samples:

| | median |
|---|---:|
| `cdclt_solve_php_6_7` | **2.4956 ms** (CI 2.4896–2.5026) |
| `proof_sat_solve_php_6_7` | **2.5806 ms** (CI 2.5743–2.5881) |

`CdclT` is **3.4% faster** than the native core on the shared pigeonhole
fixture, with disjoint intervals. S1 and S1b closed the Boolean-search gap by
porting the watch scheme, the order heap and the minimizer into `CdclT`
verbatim, and there is nothing of it left to close. (The `proof_sat_solve` bench
records its DRAT stream and `CdclT` emits none, which is the obvious candidate
for the remaining 3.4% — but that is a hypothesis, not something measured here.
Not interleaved either, and the host carries other lanes, so read the figure as
"no remaining gap" and not as a precise one.)

**So S7's brief should stop pricing the engine move as a performance win.** What
it buys is proof output — an ADR-1704 artifact `CdclT` structurally cannot
produce — and the deletion of a duplicated engine.

And read this benchmark against the population result below, because they point
opposite ways: on `php_6_7` the native core is 3.4% slower, while on the 50-file
QF_IDL population it decides four more files and takes PAR-2 down 12.9%. A
42-variable pigeonhole formula does not predict a 330,000-variable skeleton.
Whatever the population gain is, it is not the Boolean inner loop these two
benchmarks share, and locating it is a measurement the next slice should make
before it moves another route on the strength of this one.

### The two scoring populations

Idle s5 (load 0.00 before the run, nothing else on the box), `taskset -c 0-7`,
`--timeout-ms 24000` inside a `timeout -k 2 30s` hard-kill backstop, arms
**interleaved per file**. BEFORE = `fcc988900` (`main`), AFTER = this lane;
binaries confirmed different — BEFORE `sha256=7c5f5329…`, AFTER
`sha256=43060a5e…`.

The run uses `smtcomp_cli` **without** `--evidence`, i.e. the dispatcher path,
where artifact recording is off. That is the default every caller gets, so these
numbers price the engine swap and not the proof. The recording path is priced
separately and only by whoever asks for evidence.

**`qf_lra_population.tsv` is this lane's negative control, and deliberately so.**
Only the difference-logic route moved; `lra_theory` still builds `CdclT`. A
QF_LRA file reaches the moved code only when the DL probe takes it, so that
population measures collateral damage and host noise rather than the change.

Backing data, the harness and the analyser:
[`bench-results/s7b-engine-unification-20260907/`](../../../bench-results/s7b-engine-unification-20260907/README.md).

| population | decided before | decided after | PAR-2 before | PAR-2 after |
|---|---:|---:|---:|---:|
| QF_IDL (50) | 27 | **31** | 1,170,341 ms | **1,018,931 ms** (−12.9%) |
| QF_LRA (33) | 7 | **8** | 1,278,804 ms | **1,254,037 ms** (−1.9%) |

**Zero verdicts contradict `declared` in either arm of either population, and
nothing decided before went undecided after.** The four QF_IDL files gained are
`qlock-4-10-27.induction.cvc` (21,331 ms `unknown` → 11,123 ms `sat`),
`qlock-4-10-33.induction.cvc`, `queen31-1` and `super_queen29-1`; all four are
declared `sat` and all four came back `sat`.

The QF_LRA control moved by one file, `no_op_accs.base` (24,135 ms `unknown` →
23,634 ms `unsat`, matching its declared status), which is the expected shape:
`lra_theory` still runs `CdclT`, and a QF_LRA file reaches the moved code only
when the difference-logic probe takes it. One of thirty-three, at the very edge
of the budget, is a probe hit and not an `lra_theory` result.

The BEFORE arm's **27/50 on QF_IDL is exactly what S1b recorded as its AFTER**,
on the same population and the same host. So the baseline reproduces across S2,
S4 and S7a, and the +4 here is this lane's and not accumulated drift. QF_LRA is
one file off: S1b recorded 8/33 where this run's BEFORE arm gets 7/33. Both
figures are at the budget edge (the file in question is decided in ~23.6 s of a
24 s budget in the arm that gets it), so read the QF_LRA row as "flat, plus one
probe hit" and not as a two-file swing.

The analyser's exit status depends on the finding — a contradiction of
`declared`, or a decided-then-undecided file, is a nonzero exit. Run against a
synthetic two-row file carrying one of each it exits 1, so the clean result is a
live check and not a decoration.

## Gates

`test -p axeyum-solver --lib --features full -- --test-threads=6` **1,475
passed, 0 failed** (227.92 s) · `--features full --test corpus_regression` 1 ·
`--test cdclt_lia_online` / `cdclt_lra_online` / `cdclt_online` **9 / 9 / 8** ·
`test -p axeyum-cnf` **490 lib** + every suite · the three z3 differential
fuzzes at nonzero counts **5 / 1 / 1** · `check --workspace --all-targets
--all-features` clean · `clippy --workspace --all-targets --all-features -D
warnings` clean · `cargo fmt --all --check` clean.

**`--test-threads` is load-bearing on the solver sweep, and that is a finding.**
At the default 16 it stalls partway through the heavy `reconstruct::` kernel
tests, which run fine on their own (`signature` 22 tests in 162 s,
`zero_product` 7 in 157 s). That is the cgroup memory ceiling
`cargo-serialized.sh` imposes, not a hang — this route's extra allocation is
enough to tip a 16-way parallel sweep over it. A resumer who sees the sweep
"hang" should lower the thread count before bisecting.

`--test progress_frontier --features full -- --test-threads=1` **12 passed, 0
failed**, no `REGRESSION`. The one family whose regenerated artifact was read
before the revert is `nia_unsat`: frontier **40**, baseline **40**, load 1.43 →
1.54, calibration 128.2 → 136.0 ms against a 127.0 ms reference, so the run was
in frame. The other four families' numbers were **not** read — the suite passing
is the claim, not a per-family figure. No baseline was raised and
`bench-results/frontier/*.json` was reverted rather than committed. · `./scripts/check-links.sh` all links ok ·
`build --target wasm32-unknown-unknown -p axeyum-solver` clean (its three
dead-code warnings are pre-existing and about `layers.rs` /
`memory_budget.rs`, not this change).

`scripts/check-merge-hygiene.sh` reports exactly one failure, `gen-plan.py
--check`, and that is this file: a new lane status doc makes `PLAN.md` stale
until the generator runs. The lane was told not to run it; the coordinator
regenerates.

## What S7b still has to do

- **Step 4 is not done: `CdclT` is still the engine for six of the seven
  one-shot routes**, and for `ufbv_online`, which needs the incremental
  protocol. `lra_theory`, `lia_theory`, `euf_egraph`, `string_theory`,
  `uflra_online` and `uflia_online` are each a two-line change against
  `solve_native` plus a model-accessor swap — the same diff `dl_online` took —
  but each needs its own population or suite measurement, because the MBQI
  finding above says a model change can cost a verdict on a consumer that reads
  the model.
- **The trust step is not observable at corpus scale.** `smtcomp_cli
  --evidence` prints `kind=`, `certified=`, `recheck=` and `arena=` and does
  NOT print `trusted_steps`, so "how many QF_IDL refutations now carry an
  ADR-1704 step" cannot be counted from a sweep — only asserted per query from
  a test. Adding a `trusted=` field is a two-line change to
  `evidence_report_line`, but at least four things parse that line
  (`parity-run.sh`, `check-evidence-portability.sh`, a Python test, and several
  pinned transcripts in docs), so it needs its own change and its own check.
- **The evidence side is wired for one route only.** `dl_decided_report` is the
  only caller of `with_artifact_recording`. Every other route that moves needs
  the same two lines, or it will move the engine and keep the empty ledger slot.
- **The incremental protocol (S7a step 3) is still unported**, and now has a
  known single client. `CdclT::active` maps onto the native core's `branchable`
  and `activate_variables` onto `heap_insert`; what has no counterpart is
  `pending_clauses` — the one full evaluation a clause inserted under an
  assignment needs — and the atom↔variable map, which the adapter now shows how
  to keep outside the core.
- **`CdclT` cannot be deleted yet**, so the duplicate-engine cost this slice was
  meant to remove is still being paid.
- **A theory-contract violation now PANICS on a shipping route, where it used
  to be absorbed.** `Cdcl::install_theory_lemma` `expect`s that an explanation
  contains the literal it justifies and that every other literal is currently
  false; `CdclT` made no such assertion. Moving a route onto the native core
  therefore converts a class of theory bug from "wrong-ish behaviour" into a
  crash. That is the right trade for correctness and the wrong one for a
  service, and it should be revisited — declining with `Unknown` is strictly
  safer than either. The evidence that `DlTheory` respects the contract is
  behavioural and reasonably broad: 50 `dl_online` tests, `corpus_regression`,
  the full 1,475-test solver sweep and 50 QF_IDL + 33 QF_LRA corpus files, none
  of which panicked. It is not a proof, and no other theory has been exercised
  this way at all.

<!-- plan-section: landed-changes -->

| 2026-09-07 | `b963f72fd` | `axeyum_cnf::NativeLayerStats`: the fifteen driver-side fields of `TheoryLayerStats`, ported into the native core at the same increment sites, opt-in through `solve_with_theory_and_drat_proof_traced` so an unmeasured run is all-zero rather than a partial measurement. Validated before anything moved: the `CdclT` instrument reproduces S1b's `RVpredict_13` numbers exactly (2,364,618 decisions, 3,415 theory conflicts, 17 restarts, `sat`) on idle s5, and the shipping SAT DRAT stream is byte-identical at 38,333 bytes / `84a620da…`, the digest S6 and S7a each recorded. Six tests over a Boolean-satisfiable fixture the theory alone refutes. |
| 2026-09-07 | `24cb85901` | `native_cdclt::NativeTheoryAdapter` lets a `TheorySolver` drive the native core, negating the two literal conventions once at the boundary and owning the atom↔variable map. Gated by a differential — 4,000 random instances × 2 explanation channels, all also decided by an independent brute force — which found two real defects: `CdclT` recorded a lazily-propagated literal's handle after assigning it, so a theory that conflicts on its own propagation panicked in 1-UIP analysis; and the native core asked `explain` for a CORE where the handle stood for a REASON, which through an asserted-literal adapter installs `¬antecedents` as an ADR-1704 input clause the theory does not entail — a wrong-`unsat` shape. Corrects S7a's scoping twice: the adapter cannot be a blanket impl (orphan rule), and the incremental protocol has one client (`ufbv_online`), not ten. |
| 2026-09-07 | `d5a711ed1` | `dl_online` runs the native core, and `evidence::dl_decided_report` attaches the trust step its refutation now carries: `SatRefutationModuloTheory`, never certified, where the report previously had `trusted_steps` EMPTY. Two end-to-end `produce_evidence` tests, the `sat` one the control for the `unsat` one. Mutation controls for both defects, run in a private tree with the baseline bracketing green — and the first fixture did not reproduce its own defect on the first attempt (it put the conflict at level zero, where analysis never walks), which the control caught. |
| 2026-09-07 | `f429b3b8a` | The swap has to carry `CdclT`'s heuristics: the native core decides FALSE first and rephases, `CdclT` decides TRUE first and does not, and that alone took an MBQI test from `Sat` to `Unknown` because MBQI reads its instantiation terms out of the model it is handed. `TheorySolveOptions` spells the knobs out with the one-shot SAT defaults unchanged. Proof recording is off by default and budgeted when on (8M literals), because recording every learned clause of a long search is what `CdclT` never paid; `TheorySolveOutcome::Unsat(Option<_>)` keeps "not recorded" distinct from "nothing was assumed". |
| 2026-09-07 | `9a6786e84` | Both scoring populations, idle s5, arms interleaved, binaries confirmed different: QF_IDL 27/50 → **31/50** decided and PAR-2 **−12.9%**, QF_LRA (the control, `lra_theory` unmoved) 7/33 → 8/33 and −1.9%. Zero verdicts contradicting `declared`, nothing lost. Backing data, the harness and an analyser whose exit status depends on the finding are committed together. Also: `cdclt_solve_php_6_7` 2.4956 ms vs `proof_sat_solve_php_6_7` 2.5806 ms — `CdclT` is 3.4% FASTER on the shared micro-benchmark, so the Boolean-search gap S7 set out to close is already closed and the engine move must be priced on proof output, not speed. |
