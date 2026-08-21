# Budget-driven theory-core minimisation — the shipped form of gap #1's one confirmed fix

Status: **landed 2026-08-21** in `crates/axeyum-solver/src/dpll_lia.rs`.

This is the construction half of the
[linear-arithmetic deficit diagnosis](linear-arithmetic-deficit-diagnosis-2026-08-21.md).
That note measured the defect and its yield in a private snapshot, and said
explicitly that the constant its A/B moved is **not** the fix to ship:

> The shipped change should instead make minimisation **budget-driven rather than
> width-gated**: minimise while wall clock and oracle calls remain, and fall back
> to the `Large` bucket only when the budget is genuinely gone.

That is what landed. Everything below is measured on this host, at this commit,
with the diagnosis's A/B re-run beside it as the control it has to beat.

---

## 1. The defect, in one paragraph

`theory_conflicts_for_indices` refused to run deletion minimisation on any
conflict core wider than `MAX_MINIMIZED_THEORY_CORE_ATOMS = 128`, on the correct
reasoning that a pass costs one conjunctive theory-oracle call per atom. Width is
a **proxy** for that cost, and it fails in the worst available direction: an
unminimised core is charged in full against
`MAX_DYNAMIC_LARGE_CORE_LITERALS = 8_192`, the budget that exists because 24
retained clauses of ~430 literals once grew `BatSat` from 1.8 GiB to an 8 GiB
abort. So the cores too wide to minimise were exactly the cores whose width then
exhausted the retention budget, and the solve declined for want of the narrow
clauses it had refused to narrow — reporting `core_src_minimized=0` beside
`core_src_large=24` with **95 % of its wall clock unspent**.

## 2. What replaced it, and why in those units

Two jobs were sharing one constant. They are now separate.

**Whether to *attempt* minimisation** is rationed by
`MINIMIZATION_ORACLE_CALL_BUDGET`, a deterministic work budget counted in
**conjunctive theory-oracle calls**, cumulative over one `IncrementalArithDpll`
(the same lifetime as the retention budget it is paired with). One deletion
candidate is exactly one oracle call, so the unit is both machine-independent and
directly proportional to the cost being rationed.

Wall clock was the obvious alternative and is the wrong unit here. **Determinism
is a public API promise** in this repository — stable iteration order, explicit
seeds, explicit resource limits — and a wall-clock ration would make the learned
clause set, and therefore the verdict on a marginal instance, a function of
machine load. The pre-existing deadline poll inside `minimize_core` stays as the
**outer safety bound**, because a single oracle call can run for tens of seconds
and no work budget can interrupt work already in flight; it is simply no longer
the only thing bounding this work. Exhaustion is not an error: a partially
minimised core is still a valid conflict core (the pass starts from the full
inconsistent set and only ever drops atoms whose removal was re-verified
`unsat`), so the budget degrades core quality and never soundness — the same
contract the deadline already had.

Size: fully minimising every wide core the measured `QF_UFLIA` solves produce
costs ~8.4k calls (24 cores of ~351 atoms). The constant is
`4 * MAX_DYNAMIC_LARGE_CORE_LITERALS = 32_768` — four full deletion passes over
the entire retained-wide-literal budget, which covers that with headroom for
solves several times as conflict-heavy while keeping the worst case bounded by a
number rather than by a clock. **Where that constant actually sits relative to
demand is unmeasured**, and §3.1 says why the instrument could not see it.

**Which cores are charged to the retention budget** is now decided by the core's
**retained width** (`WIDE_THEORY_CORE_ATOMS`, still 128), not by whether
minimisation was attempted. This is the half that keeps the memory protection
honest. `MAX_DYNAMIC_LARGE_CORE_LITERALS` rations what the warm propositional
solver actually receives, and a core that *was* minimised and is still 300
literals wide costs `BatSat` exactly what an unminimised one of that width costs.
While minimisation was width-gated the two notions agreed — "minimised" implied
"narrow" — which is why the accounting could key off provenance. They no longer
agree, and width is the one that matches the hazard.

Note what this does **not** do: it does not exempt wide cores from the retention
budget in exchange for the gain. Against the status quo it is strictly stronger
protection at the same threshold — same 128, same 8 192, plus a chance to narrow
the core before charging it. The simple constant bump (128 → 4 096) buys its
files precisely by making wide cores stop counting, which is the trade this
version declines to make. It still wins; see §3.

---

## 3. Measurement

**Instrument.** The same one the diagnosis used, unchanged:
`target/release/examples/uf_unknown_probe`, which calls the same `solve_smtlib`
the shipped `smtcomp_cli` calls but prints the `UnknownReason` the competition CLI
is required to suppress. 24 s wall budget, 12 GiB address-space cap, external kill
at 32 s. Population: the committed, pinned competition lists
`bench-results/parity-lists/{QF_UFLIA,QF_IDL}.txt`, sha256 `f88e67890fae` /
`d7c9713a0280` — identical to the hashes in the `PARITY.md` entries these ratios
come from, so this is the same population, not a re-sample.

**Design.** Three axeyum binaries and z3 4.13.3, and every file's four runs are
**adjacent in time**. This matters on a shared box: run arm-by-arm, and machine
contention is assigned to whichever arm happened to run during a busy window.
Interleaved, it is shared. The three arms are

| arm | build |
|---|---|
| `base` | unmodified, at the snapshot commit |
| `ab` | the diagnosis's A/B: `MAX_MINIMIZED_THEORY_CORE_ATOMS` 128 → 4 096, nothing else |
| `budget` | this change |

**Positive control, before any sweep.** On
`mathsat/EufLaArithmetic/medium/medium10.smt2` the `base` binary declines at
12.9 s with `core_src_minimized=0, core_src_large=24, core_large_literals=8426`
— the exact decline string the diagnosis records — and both patched binaries run
the full 24 s budget on the same file. Behaviour changed, and it changed the same
way for both patches.

### QF_UFLIA — 200 files

| arm | decided | vs base | vs z3 | vs declared `:status` |
|---|---:|---:|---|---|
| base | 92 | — | 0 disagreements / 92 compared | 0 / 92 |
| ab (128 → 4 096) | **112** | **+20 / −0** | 0 / 112 | 0 / 112 |
| **budget (shipped)** | **114** | **+22 / −0** | **0 / 114** | **0 / 114** |

z3 decides 185 of the 200.

- **The diagnosis's A/B reproduces.** It measured 92 → 109 (+17) on a loaded
  8-way sweep; here the same one-constant binary gives 92 → 112 (+20) on a
  5-way interleaved run. The baseline is *identical* (92), the direction and
  magnitude match, and the difference is contention on marginal files — the
  diagnosis flagged its counts as a lower bound for exactly this reason.
- **The shipped version strictly dominates the constant bump on this
  population.** It decides every file `ab` decides, plus `hash_uns_04_11.smt2`
  and `xs_21_31.smt2`; it loses none. That is the interesting result, because
  `budget` keeps the memory protection `ab` gives up.
- **All 22 newly decided files agree with z3 and with the benchmark's declared
  `:status`, on all 22.** Not "z3 was undecided on some": z3 decides all 22 and
  all 22 declare a status.
- **No cross-arm verdict conflict on any of the 200 files**: nowhere do two arms
  both decide and disagree.

The diagnosis's `I1` class reproduces exactly, down to its headline number:
**48** `base` files decline with `lazy function-consistency CEGAR inconclusive`,
z3 decides **all 48**, and their median `base` wall time is **1 163 ms of a
24 s budget** — the "median 1.3 s" the diagnosis reports. **20 of the 48 are now
decided** (19 `sat`, 1 `unsat`) against the constant bump's 19.

### 3.1 The targeted decline class is gone, and the budget's operating point is unmeasured

Counting decline *strings* across the 200 QF_UFLIA runs, per arm:

| decline | base | ab | budget |
|---|---:|---:|---:|
| `retained N literals in unminimized theory cores` | **31** | **0** | **0** |
| `lazy function-consistency CEGAR inconclusive` | 48 | 17 | 17 |
| `pre-SAT skeleton exceeds the joint resource boundary` | 17 | 17 | 17 |
| `preprocessed dispatch timeout after reduced solve` | 34 | 45 | 43 |

The `base` column reproduces the diagnosis's `I1` class exactly: **48** files, the
number it reports. After the change that class is 17, and **every one of the 17
is the pre-SAT skeleton envelope** — `MAX_PRE_SAT_ARITH_ATOMS` /
`MAX_PRE_SAT_CNF_VARS`, a different constant and the diagnosis's separate `S2`
class. The decline this change targets does not occur once in 200 runs of either
patched binary.

That is the strong form of the result, and it comes with a gap I would rather
name than paper over. The `min_oracle_calls` / `min_oracle_budget_left` /
`min_declined_cores` counters print only in the two *in-loop* resource declines,
and neither fired anywhere in the sweep — the retention decline is gone, and the
timeout decline is destroyed on the way out by `dispatch_reduced`, which
substitutes a generic `preprocessed dispatch timeout after reduced solve` for
whatever the inner route said (diagnosis §2, runner-up #4). So **zero rows carry
the counters**, and I cannot report a spend distribution. What can be said is
narrower and still useful: if the budget were binding hard, cores would again be
retained unminimised, charge the retention budget by width, and reproduce the
decline in row 1 — which is 0 in 400 patched runs. An incidental confirmation
that the erased `unknown` reason is a real cost: it cost this measurement.

### QF_IDL — 200 files, the control

`dpll_lia` is on QF_IDL's route ladder too, so the change had to be shown not to
hurt a division it does not help.

| arm | decided | vs base | vs z3 | vs declared `:status` |
|---|---:|---:|---|---|
| base | 66 | — | 0 disagreements / 64 compared | 0 / 66 |
| ab (128 → 4 096) | 66 | +0 / −0 | 0 / 64 | 0 / 66 |
| **budget (shipped)** | 65 | **+0 / −1** | 0 / 63 | 0 / 65 |

z3 decides 131 of the 200. Again **no cross-arm verdict conflict on any file**.

The single loss is `diamonds/diamonds.12.2.i.a.u.smt2`, and it is worth being
precise about rather than waving at contention. Re-run in isolation on a quieter
box (load 6–7 rather than the sweep's 15–18), three times each:

| arm | verdict | wall |
|---|---|---|
| base | `unsat` | 11 622 / 11 722 / 11 822 ms |
| ab | `unsat` | 11 621 / 11 722 / 11 822 ms |
| budget | `unsat` | 12 924 / 13 124 / 12 922 ms |

All three decide it, reproducibly, well inside the 24 s budget. So this is not a
capability loss — but it is not *nothing* either: the shipped arm is about **11 %
slower on this file**, because it now does minimisation work the width gate used
to skip. Under the 5-way sweep at load 15+ that margin was what pushed a
15-second file past the external 32 s kill. A file this close to the wall will
flip either way on a loaded box; the honest statement is that the change costs
measurable time on QF_IDL and buys nothing there, which is exactly what a control
is for.


---

## 4. Guards, and what mutation testing could and could not show

Every guard was deleted in turn and the `dpll_lia` unit suite re-run; the
standard is that **exactly one** test dies.

| mutation (guard deleted) | tests killed | which |
|---|---:|---|
| `if !budget.charge() { break; }` → `budget.charge();` | **1** | `the_minimization_budget_bounds_deletion_work_in_oracle_calls` |
| delete the whole budget-exhausted arm at the decision point | **1** | `an_exhausted_minimization_budget_retains_the_core_unminimized` |
| delete `budget.note_declined_core();` | **1** | `an_exhausted_minimization_budget_retains_the_core_unminimized` |
| drop `Minimized` from the retention charge | **1** | `a_minimized_but_still_wide_core_consumes_the_retention_budget` |
| drop `&& len > WIDE_THEORY_CORE_ATOMS` from the retention charge | **1** | `narrow_retained_cores_do_not_consume_the_retention_budget` |
| drop `Large` from the retention charge | **1** | `wide_theory_core_budget_declines_before_another_sat_round` (pre-existing) |
| re-instate the width gate (`\|\| indices.len() > WIDE_THEORY_CORE_ATOMS`) | **1** | `a_core_wider_than_the_old_width_gate_is_minimized` |
| delete the `past_deadline` arm at the decision point | **0** | — see below |

Seven of eight kill **exactly one** test, and each kills a *different* one except
the two mutations of the same arm. The suite is 39 tests
(`cargo test -p axeyum-solver --features full --lib -- dpll_lia`); every run above
reports `38 passed; 1 failed`, so nothing else moved. The last row was verified
twice, before and after `rustfmt`, because reformatting changed the anchor text
and a mutation harness whose anchor silently misses is a harness that reports
"survived" for a guard it never deleted.


One mutant survives, and it is worth naming rather than hiding. **M6**, the
`past_deadline` short-circuit at the minimisation decision point, is pre-existing
and I could not construct an input that reaches it: with an expired deadline the
top-of-function oracle call itself declines, so the function returns no cores at
all before that arm is evaluated. The arm is reachable only when the deadline
expires *inside* the cheap extractors above it, which is a timing race no
deterministic fixture can force. It is not a soundness hole — `minimize_core`
polls the same deadline itself and returns the unmodified core — so deleting the
arm would change a provenance tag and one vector copy. The test
`an_expired_deadline_spends_no_minimization_work` records the behaviour and says
in its doc comment why it is a characterisation and not a guard.

And the standing caveat, which applies here as everywhere: **mutation testing
measures the guards that exist, never the ones that are missing.** What it does
establish is that none of these seven is shadowed by another rejecting the same
input, which is the failure mode that let six of seven guards in another suite be
deleted with everything still green.

---

## 4.1 The capability ratchet

`cargo test -p axeyum-solver --test progress_frontier --features full --
--test-threads=1 --nocapture`, run on the quiet box (load 3.1–4.2), **10 tests,
0 failed**:

| family | frontier | baseline | verdict |
|---|---:|---:|---|
| `bv_reduction` | 38 | 30 | PROGRESS, ratchetable |
| `lia_cuts` | 35 | 26 | PROGRESS, ratchetable |
| `nia_unsat` | 40 | 40 | at floor |
| `nra_degree` | 40 | 40 | at floor |
| `string_bound` | 40 | 8 | PROGRESS, ratchetable |

**Read the reference frame before believing any of that**, which is the whole
point of those lines: calibration 138.6–144.8 ms against a 127.0 ms reference,
**scale 1.09x–1.14x**, inside the ratchetable window — so no run is marked NOT
COMPARABLE and none is ADVISORY ONLY. **No REGRESSION on any family**, which is
what this change had to show; `lia_cuts` is the family whose engine it touches
and it sits 9 above its floor.

The PROGRESS lines are *not* claimed for this change — `bv_reduction` and
`string_bound` have nothing to do with `dpll_lia`, and their frontiers are above
floors that no lane has raised. **No baseline is raised here.**

## 5. What this does not establish

- **The reference is z3 4.13.3, not cvc5 1.3.4.** cvc5 is not installed on this
  host. The `PARITY.md` ratios stay cvc5's, and nothing here has been through
  `scripts/parity-run.sh`, which remains the only instrument allowed to move a
  `PARITY.md` number. The projection is: the recorded QF_UFLIA entry is 94/180 =
  52.2 %, and +22 on that baseline would be 116/180 = 64.4 %. That is a
  projection from an A/B, not a parity result.
- **Two divisions, one budget, one machine.** QF_LRA, QF_RDL, QF_LIA and QF_NIA
  were not swept for this change. `dpll_lia` is on QF_LRA's and QF_RDL's ladders
  only below routes that answer first (diagnosis §3), and the workspace suites
  cover the rest, but that is an argument, not a measurement.
- **Where the budget constant sits relative to demand is unmeasured** (§3.1):
  its counters print only in declines that did not fire on this population, so
  these numbers say nothing about the right size for it. What they do say is
  that removing the *width* gate is what produced the files.

## Provenance

Measured 2026-08-21 on a 16-thread i5-12600K, sweep at `-P 5` pinned to
`taskset -c 0-11`, load average 9–17 throughout with other lanes on the box, z3
4.13.3 at `/usr/bin/z3`, cvc5 absent. All three binaries built from private
`scripts/lane-snapshot.sh` trees; per-file data in
[`bench-results/lia-core-minimisation-20260821/`](../../../bench-results/lia-core-minimisation-20260821/README.md).
