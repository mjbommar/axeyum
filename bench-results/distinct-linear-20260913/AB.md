# AB — the measurement

Lane `DISTINCT-LINEAR`, 2026-09-13. Binary
`/nas3/data/axeyum/harness/bin/axeyum-smtcomp-distinct-linear-b439597e9`, built
`--release` from `b439597e9` with no source file newer than the artefact.

The pre-registered sizing and method are in `README.md` beside this, committed
before any of the numbers below existed. The decision is ADR-2000.

## Protocol

One binary, two env values, both arms **back to back on the same file on the
same pinned core**, arm order alternating per file. 24 s wall, 8 GiB
`ulimit -v`. Six pinned core pairs — `1,9` and `3,11` on s5, s6 and s7.

**Polarity: this lever ships OFF.** `base` is `env -u AXEYUM_DISTINCT_LINEAR`;
`arm` is `AXEYUM_DISTINCT_LINEAR=on`.

## 1. The A/B

| | rows | base decided | arm decided | net | gains | losses | sat↔unsat |
|---|---:|---:|---:|---:|---:|---:|---:|
| treatment — all 356 over-cap files | 356 | 0 | 1 | **+1** | 1 | 0 | **0** |
| control — `UFLIA` pinned 200 | 200 | 68 | 69 | +1 | 1 | 0 | **0** |

All 712 solves exited 0. No `none`, no OOM, no crash, no `ulimit` kill.

Mean wall time on the treatment population: **267 ms → 21,175 ms**. The base
arm's 0.1 s is an ingest refusal; the arm's 24 s is a search that mostly does not
finish. 355 of 356 rows are `unknown → unknown`.

## 2. Both `+1`s had to be re-run, and they are not the same thing

### The control's is the machine

`UFLIA/simplify2/front_end_suite/javafe.ast.DelegatingPrettyPrint.010.smt2`,
`unknown` (24,233 ms) → `unsat` (3,311 ms).

`UFLIA`'s largest `distinct` arity is **256**, inside the pairwise cap, and this
file's is **47** — the arm cannot change one byte of what is parsed. Re-run 3×
per arm: **STABLE-SAME**, `unsat` 3/3 in *both* arms. The A/B's base run lost to
ambient load.

This is the case for running a control division the change provably cannot
touch, and for re-running every mover. A lane that reported the A/B row alone
would have published a `+1` caused by its own sweep.

### The treatment's is real, attributable, and load-sensitive

`UFNIA/spec_sharp/test14-CommandLineOptions.ssc.23.….get_ProverNeedsTypes.smt2`,
base `unknown` (109 ms) → arm `unsat` (13,720 ms).

The base arm's 109 ms is the **deterministic** cap refusal. There is no load
interpretation of a verdict the base arm structurally cannot produce, so unlike
the control row this one is attributable to the change.

Re-run 3× per arm it is **UNSTABLE** — arm decided 1 of 3, base 0 of 3. One of
three is a 95 % interval of `[2 %, 87 %]`, which is not a number, so
`mover-rate.sh` ran 15 more on a quiet pinned core:

    MOVER-RATE runs=15 arm_decided=12/15 base_decided=0/15 budget=24s
    MOVER-RATE arm mean_ms=14727

**12 of 15**, mean 14,727 ms of a 24 s budget; base 0 of 15 at a flat 109 ms.
Not a coin flip — a refutation that costs 61 % of the budget and therefore falls
off the end whenever the machine is busy, which is what the 1-of-3 re-check
measured while five other shards were running.

## 3. Verification (ADR-1957 denominators)

Both movers, three independent authorities, no-opinion counted separately:

| file | ours | `:status` | z3 4.x | cvc5 | |
|---|---|---|---|---|---|
| `UFNIA/spec_sharp/test14-CommandLineOptions.ssc.23…` | unsat | unsat | unsat | unsat | agree |
| `UFLIA/simplify2/…/javafe.ast.DelegatingPrettyPrint.010` | unsat | unsat | unsat | unsat | agree |

**0 disagreements on a comparable denominator of 3 of 3 per row, 6 of 6
overall.** Run with `bench-results/dt-exactness-20260913/verify-new-verdicts.sh`
— the copy whose `:status` stage was repaired, not the
`dispatch-decline-audit-20260913` one whose `$`-anchored grep matched nothing on
every file.

## 4. Noise floor

One arm, one code state, the `UFLIA` pinned 200, three times on six pinned core
pairs:

    run1 decided=72 of 200
    run2 decided=72 of 200
    run3 decided=74 of 200

**Band 2.** Two files churn, both `unknown unknown unsat`:
`sledgehammer/FFT/smtlib.1015458` and `sledgehammer/NS_Shared/smtlib.657037`.

The control's `+1` is inside that band.

**A second spread, larger than the band.** The A/B decided **69** of these same
200 files while running 8 shards on 4 core pairs; this floor decided **72–74**
running 6 shards on 6. Same binary, same arm, same files. *The configuration of a
sweep moves the count by more than repeating the sweep does* — so a band measured
under one shard layout does not transfer to another, and the same effect is why
the treatment mover reads 1/3 under the A/B's layout and 12/15 alone on a core.

## 5. Mutation control

200 files from the `QF_UF` and `UFLIA` `distinct`-bearing populations (120
declared `unsat`, 80 declared `sat`, drawn smallest-first so the solver decides
them), four arms, threshold lowered to 2.

| | |
|---|---|
| `base` vs `arm`, both decided and differing | **0** |
| WEAKENING mutant (`mutant:vacuous`), decided contradictions | **3** — criterion met |
| STRENGTHENING mutant (`mutant:shared`), decided contradictions | **0** — **criterion NOT met, script exited non-zero** |
| `base` decided → `arm` `unknown` at `on:2` | 60 of 80 `sat` rows |

`shared-mutant-probe.sh` then gave the strengthening mutant its best case — the
12 files where the honest arm still decided `sat` *and* ≥ 2 `distinct`
applications exist for one shared injection to collide on — at six times the
budget:

    SHARED-PROBE rows=12 arm_sat=12 decided_flips=0 budget=60s

**12 of 12 changed (`sat` → `unknown`); 0 of 12 contradicted.** The mutant is not
silent; it is never *decisive*. This solver cannot refute the contradiction it
introduces within budget, so at corpus scale this population cannot tell "wrong"
from "harder", and the zero in the first row above is evidence for the weakening
direction **only**. The strengthening mutant's decided kill exists at unit scale
(`the_shared_injection_mutant_breaks_the_sat`, `sat` → `unsat`).

The 60 losses at `on:2` are why the shipped threshold is the pairwise cap and not
a small number: replacing a cheap pairwise `distinct` with UF-into-`Int`
machinery costs verdicts wherever the pairwise path was working. At the shipped
threshold that loss mode is structurally impossible — the pairwise path refuses
every affected file by definition.

## 6. The finding

Two files, one from each family, at a **600 s** budget — 25× the board envelope —
with the arm on:

    ; give-up kind=Watchdog detail=watchdog fired before the worker thread returned
    unknown

Both. The `lahiri` file z3 refutes in 508 ms.

**The front-door refusal was never the binding constraint.** Clearing a
deterministic ingest refusal on 309 files bought one verdict that needs 61 % of
the budget, because what stops these queries is the quantified ladder, and that
is not budget-bound on this family at any budget worth giving it.
