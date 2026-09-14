# ADR-2035: two populations reach one boundary, and a round cap can convert neither

Status: accepted
Index-summary: [ADR-2030] left two populations reaching one boundary and asked for them to be split before anyone built a cap. The split is **mechanical, not a threshold**: `sat_candidates >= 1` means a round was ADMITTED past the boundary and returned a model, so the refusal is on a later round over a skeleton the batch grew (**GROWN, 10**); `sat_candidates == 0, solve_rounds == 1, lemmas_added == 0` means the FIRST solve was refused before a single lemma existed (**BORN-OVER, 12**), and on those no cap of any kind can help. Zero residue, and it agrees exactly with [ADR-2030]'s `lemmas_added >= 100` with nothing in between — the threshold was unjustified, not wrong. **The round cap is refuted by reading** (`check_with_function_consistency` has three exits and truncation can only produce `Unknown`; GROWN's round 1 returns a functionally INCONSISTENT model, `violated_pairs >= 8` on all ten), and that non-run was pre-registered. **Its cost was invisible to the census**: `FunctionConsistencyStats` escapes only through `wrap_unknown`, so deciding loops leave no round count — the census says `solve_rounds` 1–3, a probe at all three exits says **1–27**, and a cap at 1 truncates 324 deciding loops on **61 files**, at 3 still **27 files**. The censused label also covers **two code sites** with different rescue wiring, split by a `stage` suffix: **22 of 22** at `IncrementalArithDpll::solve` (no rescue), **0** at the preflight (rescue shipped) — [ADR-2020] §8.3's SECOND missing wiring, untested by [ADR-2030]. An ordered probe (`AXEYUM_PRESATPROBE`, off by default, printed and never acted on) over all 129 files on the SHIPPED path says the gap is **real**, the opposite of the first: 47 files cross, 35 only at `solve`, 12 only at `preflight`, **0 at both** — and the two sites split by family (`UFLIA` boogie/simplify vs `UFNIA` 2019-Preiner). **And closing it is worth zero**: the rescue RAN on 36 files and DECIDED on **0** (`declined` 36 of 36) — the online CDCL(T) engine will not start on an oversized skeleton, a stronger negative than any verdict count. A/B interleaved, one binary, shards fixed: **0 gains** on 129 `[0.0 %, 2.9 %]`, on the 22 targets, and on the **35 files where the lever actually runs**; the single loss is `UFNIA/sledgehammer/FFT/z3.885941`, absent from the crossing set, the same row that produced EVERY loss in both of [ADR-2030]'s arms, and it re-runs **UNSTABLE in the opposite direction** (OFF 1/3, ON 2/3). Control `QF_LIA` 200 rows with **120 decided on both arms** moves **0** -- but its non-vacuity was MEASURED rather than asserted and the measurement REFUTED the reasoning that chose it: the control crosses this boundary on 45 of 200 files and **all 45 at the OTHER site**, so `pre_sat_boundary_rescue` never executes there and that control is VACUOUS for the lever, which is labelled rather than quoted; the non-vacuous loss control is the **35 main-arm files where the rescue provably RAN**, 9 decided on both arms, 0 lost. Noise floor **0 of 129** -- stronger than [ADR-2030]'s, whose one moved row was this same `FFT/z3.885941`, which here is `unknown` in BOTH byte-identical noise arms and both probe arms and has **0 boundary crossings**, so the lever cannot reach it. **Two of this lane's own guards could not fail and the mutations found both** — the polarity fixture `x <= 0` is refused by the rescue's own difference-logic gate, so inverting the lever killed **0 of 1757**; and the one-shot test consumes the process's only rescue attempt, which would have disarmed the polarity test by running first. Three guards now, each mutation-verified at exactly one test. The **envelope archaeology**: two commits ever, current value six days old and re-derived against the engine that runs — NOT the `64` case — but fitted in 2026-08 to readmit one file, with a memory story its own re-derivation refutes (71 MiB against an 8 GiB ceiling; the control it names never reaches the gate). Correct as set; **do not raise it again**. Also measured: the boundary population is **47 files, not the censused 22**, and **8 of those 22 "declining" files are decided anyway** — sizing off that list overstates the prize by more than a third. Ships OFF. [ADR-2020]'s redirect survives: the target is the SIZE of the ground set and the axis is **selection**, which ten closed explanations still do not cover.
Index-status: accepted
Date: 2026-09-14

## Context

[ADR-2030] closed the ninth explanation for the `UFLIA`/`UFNIA` gap and left one
thing sized but unsplit: **all 16 flooded observations die at `solve_rounds=2`,
10 of them at the pre-SAT skeleton boundary that is [ADR-2020]'s largest binding
cause — and 12 of the 15 UNflooded observations reach the same boundary**, so
two populations arrive at one place by different routes and a cap addresses only
one of them. This lane was asked to split them before building anything.

Branch base: `git merge-base main HEAD` is
`ffaf920cd585300b5c3c854f88db9d8ee8517759`, which **is** local `main`'s HEAD.

Rules were [pre-registered](../../../bench-results/round-cap-20260914/PREREGISTRATION.md)
in their own commit before any A/B arm ran, together with the structural
argument that decided *not* to run one of them.

## 1. The split, by mechanism rather than by a threshold

[ADR-2030] split on `lemmas_added >= 100`. A threshold cannot distinguish *"the
flood pushed this over the boundary"* from *"this was already over and happens to
have emitted lemmas"*, and the difference is the whole question. The CEGAR loop's
own statistics decide it without a cut point:

| population | test | n | what it means |
|---|---|---:|---|
| **GROWN** | `sat_candidates >= 1` | **10** | a round's solve was **admitted** past the boundary and returned a model, so the refusal is on a LATER round, over a skeleton the lemma batch grew |
| **BORN-OVER** | `sat_candidates == 0`, `solve_rounds == 1`, `lemmas_added == 0` | **12** | the **first** solve was refused; the instantiated conjunction crossed the boundary before a single lemma existed |
| UNCLASSIFIED | — | **0** | — |

22 observations, 22 distinct files, one observation each, no residue. It agrees
exactly with [ADR-2030]'s threshold — every `lemmas_added >= 100` is GROWN and
every `lemmas_added == 0` is BORN-OVER, with **nothing in between** — so the
threshold was not wrong; it was unjustified, and now it is not.

The sizes are visible in the split table
([`split-populations.txt`](../../../bench-results/round-cap-20260914/split-populations.txt)).
BORN-OVER sits in a tight band — 14,686 to 15,832 atoms, 24,035 to 24,430 CNF
vars, i.e. **1.43x to 1.55x** the 10,240-atom envelope before any lemma exists.
GROWN spans 8,627 to 52,376 atoms, and **two of its ten are UNDER the atom
envelope** and cross only on CNF variables (`AssignToRepField` at 9,364/21,075;
`TransformQuant` at 8,627/17,066, just **4.2 %** over).

**The consequence [ADR-2030] asked not to lose, now with a reason:** on the 12
BORN-OVER files no lemma cap and no round cap can do anything at all, because
the refusal *precedes the first lemma*. That is 12 of 22, and 12 of [ADR-2020]'s
largest bucket.

## 2. The census label covers two code sites with different rescue wiring

`pre-SAT skeleton exceeds the joint resource boundary` is built by one function,
`pre_sat_skeleton_boundary_reason`, called from **two** places. The sentence is
identical but for a `stage` suffix, so a census keyed on it merges them — the
same trap [ADR-2020] hit with `;QPROBE`, one layer down. Splitting on the stage:

| stage | site | rescue | n |
|---|---|---|---:|
| `declining before the online CDCL(T) probe` | `arith_dpll_admission_preflight` | **`oversized_admission_probe` runs first** | **0** |
| `declining before the first SAT round` | `IncrementalArithDpll::solve` | **none** | **22** |

and **0 of 22** carry `reusable_arith_lemmas=`, so they did not arrive through
`check_with_arith_dpll_reusing_lemmas` either. The route is
`check_with_uf_arithmetic_lazy` → `check_with_function_consistency` →
`check_with_incremental_arith` → `IncrementalArithDpll::solve`, which reaches the
boundary and returns.

This is [ADR-2020] §8.3's **second** missing wiring, the one [ADR-2030] did not
take:

> `oversized_admission_probe` is wired only into `check_with_arith_dpll`, so the
> UF+arith route that reaches the skeleton boundary gets **no bounded
> online-CDCL(T) shot at all**.

A consequence worth stating beyond the boundary case: the CEGAR's inner solver
is `check_with_incremental_arith`, which drives `IncrementalArithDpll` directly.
`check_with_arith_dpll`'s ordinary path gives `check_qf_lia_online_cdclt` a third
of the budget *before* falling back to that loop. **Neither of the CEGAR's first
two inner routes reaches the online engine at all**, oversized or not: the
primary is `check_with_incremental_arith`, and its `Unsupported` fallback
`check_with_arith_dpll_reusing_lemmas` goes through `run_arith_dpll`, which is
the same loop. Only the third fallback, `check_auto`, could get there, and it is
reached only when both of the others return `Unsupported`. So [ADR-2020]'s
envelope null — which
admits the skeleton to `IncrementalArithDpll`'s enumerate-and-block loop and
moves 0 of 129 — does not cover the online engine on these queries.

## 3. The round cap is refuted by reading, and the non-run was pre-registered

`check_with_function_consistency` has exactly three exits:

| exit | condition |
|---|---|
| `Unsat` | the inner solve refuted the abstraction |
| `Unknown` | **the inner solve returned `Unknown`** — returned immediately, wrapped in the stats |
| replay | the candidate model was functionally consistent, so no lemma was emitted |

Truncating the loop at a cap can only produce the **second**. Therefore:

* on **BORN-OVER** the refusal is at round 1's solve, before a cap of `N >= 1`
  could fire; and
* on **GROWN** round 1 returned a model that is functionally *inconsistent*
  (`violated_pairs >= 8` on every one of the ten), so stopping there yields
  `Unknown` — which is already what happens.

**A round cap can convert nothing in this population.** Its only possible product
is wall-clock handed back to a downstream route, which PAR-2 does not score.
Recorded in the preregistration *before* measuring, so that "we did not run it"
is a stated outcome and not a quiet omission.

### The distribution anyway, on the denominator the census cannot reach

**`FunctionConsistencyStats` reaches the outside world only through
`wrap_unknown`**, so a query the CEGAR *decides* leaves no round count behind.
The committed census's `solve_rounds` therefore runs `1 .. 3` — over the
`unknown` half of the population only. `FCPROBE` emits at all three exits. Over
the whole 129-file population on the shipped 24 s path
([`round-distribution.txt`](../../../bench-results/round-cap-20260914/round-distribution.txt),
1,776 exit records on 109 files):

| deepest loop per file | exit `replay` | exit `unknown` | exit `unsat` |
|---|---:|---:|---:|
| 1 round | 12 | 29 | 1 |
| 2 rounds | 16 | 13 | — |
| 3 rounds | 9 | 1 | — |
| 4 rounds | 11 | — | — |
| 5–9 rounds | 9 | 1 (at 8) | — |
| 11–27 rounds | 7 | — | — |
| **total files** | **64** | **44** | **1** |

**The CEGAR runs up to 27 rounds, not 3.** The census's ceiling was an artifact
of its denominator.

And that is the cap's cost, measured rather than argued — 874 deciding loop
records on 83 files:

| cap | deciding loops truncated | files that lose a decision |
|---:|---:|---:|
| **1** | 324 | **61** |
| **2** | 114 | **38** |
| **3** | 87 | **27** |
| **4** | 28 | **16** |

A cap at the census's own observed maximum of 3 already costs 27 files, and the
upside was zero before any of this was run. **The round cap is not a marginal
call; it is a loss at every value.**

## 4. The boundary: calibrated, six days ago, for a job it is not doing

Full archaeology in
[`boundary-archaeology.md`](../../../bench-results/round-cap-20260914/boundary-archaeology.md).
Short form, because the "115x headroom" framing invites the wrong conclusion:

* `git log -S MAX_MODERATE_PRE_SAT_ARITH_ATOMS` returns exactly **two** commits.
  `8a6de50ac` (2026-08-10) introduced the envelope at 1,280/8,192; `832c2afd0`
  (2026-09-08) re-derived it to 10,240/16,384 **against the engine that actually
  runs**. This is not the `64` case: it is not a forgotten number, and its
  current value is six days old.
* But its **origin is not a memory bound**. The 2026-08-10 preregistration and
  result say it repairs *one* deterministic historical loss (`windowreal-17`
  moving from UNSAT to a typed resource `unknown`) while two named abort controls
  keep declining. It is a rectangle **fitted** between one file it wanted and two
  it did not.
* And its **stated justification is refuted by its own re-derivation**: peak RSS
  71.3 MiB against the 8 GiB ceiling it cites, RSS moving at most 0.5 % whether
  the envelope is enforced or removed, and `pursuit-safety-16` — the control the
  bound names — does not even reach this gate. *"The bound does not protect the
  case it names."*
* **"Above this, nobody has measured" is no longer true.** [ADR-2020] raised it
  4x and measured 0 of 129, with the refusal converting into a timeout. As a
  *time* proxy the boundary is empirically about right; as the *memory* bound it
  is documented to be, it is two orders of magnitude conservative and irrelevant.

**Verdict: correct as set, and do not raise it again** — for a reason its own
doc comment does not give. What is still owed is the shape, not the position:
the constant's own comment names [ADR-1752]'s byte budget as the real fix, and
this lane does not do it, because the measured fact is that the boundary's
position is not what costs us these files.

One pair of numbers that must not be mixed: the 2026-09-08 re-derivation reports
**3 of 10 refusals decided** when the envelope is removed, and [ADR-2020] reports
**0 of 129**. Different populations (`QF_LIA` reference-only losses vs the
`UFLIA`/`UFNIA` ground-decide set); neither transfers.

## 5. The lever that WAS measured

| lever | OFF (shipped) | ON |
|---|---|---|
| `AXEYUM_PRESATPROBE` | unset | `1` — the ordered probe; printed, never acted on |
| `AXEYUM_PRESAT_RESCUE` | unset | `1` — offer `oversized_admission_probe` at the `solve` site |

Both parse through one function that accepts an exact `1` (whitespace tolerated)
and nothing else, split from its `OnceLock` reader so the polarity is a pure unit
test.

**Both arms visible BY MECHANISM, asserted before measuring.** On
`UFLIA/simplify2/front_end_suite/javafe.ast.MethodDecl.005.smt2`, shipped 24 s
path, pinned core:

| arm | probe lines |
|---|---|
| OFF | `site=solve ... rescue=lever-off outcome=refused` **x 10** |
| ON | `site=solve ... rescue=ran outcome=declined` **x 1**, then `rescue=budget-spent` **x 9** |

`site=preflight` is **0** in both. The `atoms=15500, cnf_vars=23388` the probe
prints is the same pair [ADR-2020] recorded for this file in the shipped path,
which is an independent check that the probe is reading the gate it claims to.

**The rescue is bounded to ONE attempt per process**, and the bound is not
decoration: 10 crossings on this one file, and [ADR-2030] measured 60 to 1,605
boundary consultations on a single file through the width ladder. Unbounded,
the lever would multiply a 10 s probe budget by up to four digits and the A/B
would score the resulting harness timeouts as losses caused by the idea rather
than by the plumbing. Per PROCESS, not per query — `smtcomp_cli` runs one query
per process, a library caller does not, and that limitation is written at the
constant rather than hidden behind the word "bounded".

**The nonlinear-integer guard is reproduced, not inherited.**
`check_with_arith_dpll` rejects a nonlinear-integer query before its own
preflight, because `lia_online::is_lia_atom` accepts `(<= (* x y) c)`,
classifies it `Unsupported`, contributes no row, and the driver then enumerates
to its deadline. The `solve` site has no such guard upstream and three of the 22
files are `UFNIA`.

**Soundness.** The rescue returns a `CheckResult` in exactly the position
`IncrementalArithDpll::solve` would have returned one, over the same assertion
set. `Unsat` refutes that set; `Sat` is a model of it, which the CEGAR loop
replays and projects as it does for any inner solver — `check_auto` is already
one of the loop's own fallbacks. What changes is which engine is asked, not what
is admitted.

## 6. Two guards of ours could not fail, and the mutations found both

Three guards, each deleted in turn against the **full 1757-test lib sweep**:

| deleted guard | tests killed |
|---|---:|
| `parse_pre_sat_flag` widened to accept anything | **1** |
| the lever's polarity inverted so the rescue always runs | **1** |
| the one-shot attempt no longer consumed | **1** |

The middle row is the interesting one, because **its first version killed zero**.

1. **The polarity fixture could not fail.** It used `x <= 0`, which
   `oversized_admission_probe` refuses at its own `is_difference_logic_shape`
   gate *before* reaching the online route — so it returned `None` in both arms
   for a reason that has nothing to do with the lever. Inverting the polarity
   killed **0 of 1757**. The fixture is now `2x + 3y <= 5 /\ 2x + 3y >= 6`,
   outside the difference-logic fragment, with a companion control asserting the
   rescue **does** decide it. Only then did the mutation kill exactly one test.
2. **The one-shot test disarms the polarity test if it runs first**, because it
   consumes the process's only rescue attempt — leaving the polarity test's
   rescue refused by the BUDGET rather than by the lever. Both now take a lock
   and reset the counter. This one was caught by reading, before it shipped, but
   it is the same shape and is recorded next to it.

A third guard fired on its own: `config_registry`'s
`every_governing_constant_is_registered` rejected `MAX_PRE_SAT_RESCUE_ATTEMPTS`
until it carried a dated justification. It is registered with the measurement
above.

## 7. Gate 0: the ordered probe answers the question before the A/B does

Pre-registered: *the A/B is not believed until an ordered probe separates
"never reached the rescue" from "reached it and came out the other side"*.
All 129 files, shipped 24 s path, one binary, four pinned cores on s7, both arms.

### The missing wiring is REAL — unlike the one [ADR-2030] refuted

| | OFF (shipped) | ON |
|---|---:|---:|
| files crossing the boundary at all | **47** | 48 |
| ...only at `site=solve` (**no** rescue) | **35** | 36 |
| ...only at `site=preflight` (rescue shipped) | **12** | 12 |
| ...at **both** sites | **0** | **0** |
| total `site=solve` crossings | 160 | 157 |
| total `site=preflight` crossings | 65 | 65 |

**Zero of 47 cross at both sites.** The reading that killed [ADR-2020]'s first
missing wiring — "it reached the rescue and came out the other side" — is false
here, at 0 of 47. And the two sites serve populations that split cleanly by
family: `UFLIA` `boogie`/`simplify` at `solve`, `UFNIA` `2019-Preiner` at
`preflight`. The wiring gap is real and it is a whole family wide.

### And the lever still cannot gain, for a mechanical reason

With `AXEYUM_PRESAT_RESCUE=1` the rescue **ran on 36 files and decided on 0**:

| outcome | n |
|---|---:|
| `sat` | **0** |
| `unsat` | **0** |
| `declined` | **36** |

`check_qf_lia_online_cdclt` refuses every oversized skeleton it is handed. This
is a stronger negative than a verdict count: the engine swap does not *fail to
help*, it never produces an answer at all. [ADR-2020] showed that admitting
these skeletons to `IncrementalArithDpll`'s enumerate-and-block loop converts a
refusal into a timeout; this shows the online CDCL(T) engine will not even
start on them.

### Two things the census could not have told anyone

1. **The boundary population is more than twice the censused one.** The census
   names 22 files; the shipped path crosses on **47**. The other 27 cross this
   boundary and then give up somewhere else, so the census — which records only
   the LAST site to refuse — never names them.
2. **20 of the 22 censused targets do cross on the shipped path**, so the
   replay-probe/shipped-path mismatch is **not** an explanation for the earlier
   nulls. But **8 of those 22 files are DECIDED overall** on the shipped path —
   the boundary refuses inside them and another route answers anyway. A file on
   the "declining ground checker" list is not a file we fail to decide, and
   sizing work off that list without this correction overstates the prize by
   more than a third.

## 7b. The A/B

Interleaved per file, **one binary** (sha256 `3f44051a…`, printed by every
runner and re-verified on each host after copying), two env values, arms back to
back on the same pinned core with the order rotating per file, **both arms
inside each shard**. 24 s budget, `ulimit -v` 8 GiB, `timeout 40 s`.

**Shard configuration, fixed across arms:** main = s5 cores 1/3/5/7;
control = s6 cores 1/3; noise floor = s5 cores 1/3/5/7 **after** the main arm
finished. Peak concurrent pinned cores: **8**.

> **Deviation from the preregistration, recorded rather than smoothed over.**
> The noise floor was pre-registered on s7 cores 1/3. It was started there,
> reached 9 of 129 rows, and was killed and restarted as four shards on s5 for
> throughput. Both arms still run back to back inside one shard on one core, so
> the arm comparison is unaffected; what changed is the host and the shard count,
> and it changed for the noise floor only.

| arm | rows | OFF decided | ON decided | GAIN | LOSS | FLIP | wall |
|---|---:|---:|---:|---:|---:|---:|---:|
| **main** `UFLIA`/`UFNIA` | **129** | 10 | 9 | **0** `[0.0 %, 2.9 %]` | 1 `[0.1 %, 4.3 %]` | **0** | 1.009x |
| ...the 22 censused targets | 22 | 8 | 8 | **0** `[0.0 %, 14.9 %]` | **0** | 0 | — |
| ...**the 35 files where the lever RUNS** | 35 | 9 | 9 | **0** `[0.0 %, 9.9 %]` | **0** | 0 | — |
| ...files crossing at either site | 47 | 9 | 9 | **0** `[0.0 %, 7.6 %]` | **0** | 0 | — |
| **control** `QF_LIA` | **200** | **120** | **120** | **0** `[0.0 %, 1.9 %]` | **0** `[0.0 %, 1.9 %]` | **0** | 1.000x |
| **noise floor**, same shipped arm twice | **129** | 9 | 9 | **0** `[0.0 %, 2.9 %]` | **0** `[0.0 %, 2.9 %]` | **0** | 0.998x |

**The lever is inert exactly where it fires** — which the probe had already said
by mechanism.

### The control, and why it is not the one [ADR-2030] used

The lever fires **only** on a boundary crossing, and at the `solve` site a
crossing currently returns `Unknown` unconditionally. So a loss cannot come from
a changed verdict on a currently-decided row; it can only come from **budget** —
`oversized_admission_probe` may spend up to 10 s, and a file that today gives up
fast at the boundary and is then decided by a LATER route can be starved.

A `QF_BV` control of [ADR-2030]'s kind would be **structurally blind** to that:
BV never reaches `dpll_lia.rs`. `QF_LIA` was chosen because it drives
`IncrementalArithDpll::solve` on every row, and it has real power to detect a
loss — **120 rows decided on BOTH arms**, against [ADR-2030]'s 57 and
[ADR-2020]'s 6 all-`unknown` rows. It moves **0 of 200**.

**Its non-vacuity is measured, not asserted — and the measurement REFUTES the
reasoning that chose it.** A probe sweep over the same 200 files with the rescue
ON:

| | |
|---|---:|
| control files crossing the boundary | **45 of 200** |
| ...at `site=solve`, where the lever lives | **0** |
| ...at `site=preflight`, which already has a rescue | **45** |
| total `site=preflight` crossings | 368 |
| **files where the rescue RAN** | **0** |

`QF_LIA` does drive `IncrementalArithDpll::solve`, and it does cross this
boundary — 45 files, 368 times — but it crosses at the **other** site, every
time. **So `pre_sat_boundary_rescue` never executes on the control at all, and
the control is VACUOUS for the lever's direct effect.** It shows the rest of the
build is unchanged; it cannot detect a loss the lever caused. A control that
cannot fail is worse than no control, so it is labelled rather than quoted.

**The non-vacuous loss control is the sub-population inside the main arm**: the
**35 files where the probe recorded the rescue actually RUNNING (36 executions)**.
Nine of those rows are decided on the OFF arm and all nine stay decided on the
ON arm — 0 loss with direct execution evidence, though with only nine decided
rows its power is small, and that is stated rather than dressed up.

An architectural fact falls out of the same measurement, and it is the cleanest
statement of the wiring gap: **the `preflight` site serves the `QF_LIA` route and
the `solve` site serves the UF+CEGAR route, and they do not overlap** — 0 of 47
in the main population, 0 of 45 in the control. The rescue was wired to one of
the two routes.

### The one moved row is the same volatile row as last time

`UFNIA/sledgehammer/FFT/z3.885941.smt2` is the row that produced **every** loss
in **both** of [ADR-2030]'s arms, with different code, and then inverted under
re-runs. Three independent reasons it is not this lever's:

1. It is **absent from the 47-file crossing set**, so `pre_sat_boundary_rescue`
   is never reached on it. *Caveat stated rather than hidden:* the crossing set
   was measured on s7 and the A/B ran on s5, and whether the width ladder
   reaches the boundary inside the budget is timing-dependent, so this is strong
   attribution and not a proof.
2. The 3x-per-arm re-run classifies it **UNSTABLE** — and in the direction
   *against* the loss: OFF decided **1 of 3**, ON decided **2 of 3**.

   | | 1 | 2 | 3 |
   |---|---|---|---|
   | OFF | unknown | unknown | unsat |
   | ON | unknown | unsat | unsat |
3. **It is `unknown` in every other observation of it taken here**, including
   both arms of the byte-identical noise floor:

   | run | code | OFF | ON |
   |---|---|---|---|
   | main A/B | shipped vs lever | **`unsat` 2,410 ms** | `unknown` 24,131 ms |
   | **noise floor** | **identical both arms** | `unknown` 24,231 ms | `unknown` 24,131 ms |
   | ordered probe (s7) | shipped vs lever | `unknown` 24,129 ms | `unknown` 24,130 ms |

   The noise floor's OFF arm *is* the main arm's OFF arm, byte for byte, and it
   does not decide. A row whose verdict changes at fixed code cannot be
   evidence about a lever, and this row has now done so across two lanes.
   Its `crossings = 0` in both probe arms is the independent confirmation.

   **The noise floor's total is 0 of 129** — stronger than [ADR-2030]'s, whose
   band included this very row — so the band here is genuinely zero on this
   population, and the main arm's single loss is outside it.

## 8. Decision

**The round cap is not built. `AXEYUM_PRESAT_RESCUE` ships OFF.
`AXEYUM_PRESATPROBE` stays, off by default, because it is the first instrument
that can census this boundary correctly.**

The pre-registered go/no-go was **>= +3 STABLE-GAIN rows with zero
STABLE-LOSS**. It is **0** gains on every denominator, including the 35 files
where the lever actually executes.

Three things this lane establishes that are worth more than the lever was:

1. **[ADR-2020] §8.3's second missing wiring is REAL**, at 0 of 47 files
   crossing both sites — the opposite of its first, which [ADR-2030] refuted.
   **And closing it is worth zero**, because the engine it connects declines all
   36 instances it is handed. Both halves are needed: "the wiring is missing" was
   true, and it was never the constraint.
2. **The round cap is a loss at every value**, and the number that made it look
   plausible was an artifact. `solve_rounds <= 3` is what the census can see; the
   loop runs to **27**, and **61 files** decide after more than one round.
3. **The pre-SAT skeleton envelope is correct as set and must not be raised
   again.** It is six days old, its memory justification is refuted by its own
   re-derivation, and the region above it has now been measured twice
   ([ADR-2020] at 4x: 0 of 129; here, the other engine: 0 of 36). What is owed
   is its *shape*, not its *position*.

**What this does not say** is that the boundary is where the gap lives.
[ADR-2020]'s redirect survives everything measured here and is still the live
one: the reference refutes 21 of these 22 files at a median **70 ms**, nine of
them without instantiating a single quantifier. **The target is the SIZE of the
ground set, and the open axis is selection.** Ten explanations are now closed
and none of them is selection.

### Post-merge prediction, with its reason

The A/B measured **this branch**. Both levers ship OFF, and with them unset the
only difference from `main` is one `if` that is false and two `OnceLock` reads
on a path that already calls `config_registry::note_crossed`. **The predicted
post-merge value is identical to `main`'s**, and the wall ratio measured at
1.009x on the main arm is the band, not a cost: the OFF arm *is* `main`'s code.

## 9. Not measured here, and reported as "did not run"

- **The round-cap A/B: NOT RUN**, pre-registered as a non-run in §3 of the
  [preregistration](../../../bench-results/round-cap-20260914/PREREGISTRATION.md)
  before any measurement, with the structural argument that decided it and the
  distribution that would have chosen its value published anyway.
- **New verdicts against three authorities ([ADR-1957]): no new verdicts**, so
  the comparable denominator is **0/0** on each of declared `:status`,
  `z3 -T:24`, and `cvc5 --tlimit 24000`. Printed rather than omitted. No
  authority was consulted, because there was nothing to consult it about.
- **The two censused targets that never cross on the shipped path**
  (`AssignToRepField_AssignToRepField.N`, `javafe.ast.ImportDeclVec.015`, both
  GROWN) are left **unexplained**. They cross in the replay probe and not in the
  shipped path; which of the two instruments is the one to believe for sizing
  work is a question this lane raises and does not answer.
- **The `site=preflight` family** (12 `UFNIA/2019-Preiner` files, 65 crossings)
  already has the rescue and is therefore untouched by this lever. Whether its
  shipped rescue ever decides was **not measured** — the probe prints
  `outcome=pending` at that site by construction.
- **A byte-budget replacement for the (atoms, CNF vars) rectangle**
  ([ADR-1752]'s shape) was **not attempted**.
