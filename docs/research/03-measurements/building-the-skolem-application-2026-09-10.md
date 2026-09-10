# Building the Skolem application: the term arrives, the verdict does not

**Date:** 2026-09-10
**Lane:** Q6-construction
**Populations:** `bench-results/parity-losses-20260908/UF.txt` — the 32 `UF`
files we return `unknown` on and z3 refutes — and
`bench-results/parity-losses-20260906/UF.axeyum-only24.txt` — the 24 `UF` files
only we solve. Budget 24 000 ms, prebuilt release binary, `taskset -c 0-7`,
4-wide. **The box was shared and busy** (load 13 → 23 across the runs; other
lanes were sweeping the same corpus), so wall-clock absolutes here are not
comparable to an idle host and every verdict that mattered was re-run isolated
before it was believed. NAS mount was live; nothing here reproduces without it.
**Depends on:** `does-the-required-instance-enter-our-egraph-2026-09-10.md` (Q2),
`term-invention-is-off-where-it-is-needed-2026-09-10.md`, and
`why-the-instantiation-loop-produces-nothing-2026-09-10.md`.

**In one line: the construction gap closes and the verdict does not move — the
missing Skolem applications now get built on 8 of Q2's 10 "never built" files,
including the exact term Q2 named on its sharpest reproducer, the 32-file slice
still decides 1 of 32, and the pass costs a refutation we currently win in
3.6 s. DO NOT BUILD; the pass ships at `0`.**

## Summary of findings

| # | finding |
|---|---|
| 1 | **Construction was not the binding constraint.** A bounded pass that forms the missing Skolem-function applications before the loop starts raises fully-ground `!qskf_` applications in the dump from 0/0/1/6/6/10 to 229/210/111/215/120/58 on six of Q2's ten (i) files. **The 32-file slice decides 1 of 32 in both arms — gained `[]`, lost `[]`.** |
| 2 | **Q2's sharpest single observable moves, alone.** On `Hoare/uf.966336` the dump gains `(f18 f29 (!qskf_35 !sk_1 !sk_0))` — the exact chain link Q2 measured as absent — so its "0 applications of any `!qskf_` symbol to `(f19 (f20 f29) f28)`" goes **0 → 1**. Its companion observable, `unsat`, does not. Q2 said which conclusion that combination licenses: **`f29` moves from its (i) column to its (ii) column.** Construction is done there; selection is the whole remaining story. |
| 3 | **It costs a win.** `Arrow_Order/uf.558544`, isolated, one binary, one moment: OFF `unsat` in 3.6 s, ON `unknown` at the 24 s budget. On the 24-file win list the sweep also showed `TypeSafe/smtlib.1262852` lost — **that one is load, not the change** (isolated: `sat` in both arms), and the two are separated here because a sweep on a loaded box cannot tell them apart. |
| 4 | **The previously-flooded files still report ZERO term-invention rounds** (`f01`, `f05`, `f12`, `f20`, `f22`: 0 before, 0 after). This route does not re-enable invention; it bypasses it. Deliverable observable 1 is answered **no**, by construction. |
| 5 | **The earlier note's attribution to `invention_ceiling` is CONFIRMED, and I had a wrong hypothesis first.** I expected the binding gate to be the enclosing `if admitted.is_empty()`. It is not: every flooded file *does* reach an empty-admitted round — a **cap-induced** fixpoint at `ground=8192` exactly, where the cap makes every later round admit nothing — and the 4096 ceiling is what blocks invention there. |
| 6 | **`f29`'s 125 invention rounds all ran in the wrong block.** It prints exactly ONE `egraph-fixpoint` line, at `ground=273`, which Q2's block census identifies as block 1 — the **un-Skolemized** assertion set, which carries no `!qskf_` symbol at all. Blocks 0 and 2, the Skolemized ones, are deadline-bounded, never reach a fixpoint, and so never enter the invention branch. "Invention ran and formed the wrong thing" is not what happened; it ran where the right thing does not exist. |

## Why this angle, and not (a) or the ceiling

The brief named three angles. I took (b), building the application directly, on
one argument: reducing the flood (angle a) and raising the ceiling both act on
gates that sit **inside** the loop, after the flood has happened, so an arm
built on either would be testing a throttle at the same time as the
construction hypothesis. A pass placed *before* the first round is downstream of
neither. That mattered more than expected, because the hypothesis turned out to
be **false** and a mixed arm could not have shown that cleanly.

Order of work, stated because it changes how finding 5 should be read: the
placement argument came first, from reading the code; the cap-induced-fixpoint
census that turned my `admitted.is_empty()` guess into finding 5 came from the
baseline sweep, after the design and before the arm was measured. Finding 5 is a
correction I ran into, not a premise I started from.

The control the brief asked for — that the baseline is not trivially fixable by
raising `INVENTION_GROUND_CEILING` — was **not run here**; it was already run.
`term-invention-is-off-where-it-is-needed-2026-09-10.md` records item 3.5's
8x-ceiling arm at **zero** and a 120 s budget at **zero**. Reported as *did not
run by this lane*, with the prior measurement named.

## What was built

`prime_skolem_application_instances` in `crates/axeyum-solver/src/qinst_egraph.rs`:
one bounded pass, run **once before the instantiation loop's first round**.

- **Eligible universals** are the active ones whose body applies a symbol named
  `!qskf_…` (a Skolem *function*, per `quant_skolemize::fresh_skolem`) to an
  argument mentioning one of **that universal's own** bound variables. That is
  precisely the class Q2 isolated: an application that cannot exist as a ground
  term until the universal is instantiated, so no trigger can match it into
  being and no ranking can reach it. A Skolem function at an already-ground
  argument, an ordinary head, or another universal's variable is **not**
  eligible — instantiating this universal would create nothing new.
- Each eligible universal gets at most 4 instances over the existing
  `build_invention_seed_lists` seeds, staged by digit sum so the all-Skolem-first
  tuple comes first, under a total budget.
- Every instance passes the unchanged `QuantifierInstanceCertificate` gate in
  `admit_generated_ground` — the same check a matched instance passes. **No new
  trust surface**; the pass can only add facts the universals already entail.

It is behind `AXEYUM_QINST_SKOLEM_PRIME` (a decimal total) with a
`SkolemPrimeGuard` for per-thread A/B, following `GroundBudget`'s shape so one
binary runs both arms. **The shipped value is `0`.**

### Cost of the pass itself

From `AXEYUM_QPROBE=1` over the 32-file slice, 46 pass invocations on 27 of the
32 files (a file enters the loop up to three times, and the un-Skolemized entry
finds nothing eligible, as it must): **1–126 eligible universals** (median 53),
**0–144 instances admitted** (median 40), ground standing at **4–189** the
moment the pass returns (median 64). It is cheap where it runs, and the ground
figure is two orders of magnitude below the 8 192 cap — so the cost measured
below is not the pass's own traffic, it is what that traffic does to the
admission schedule downstream.

## Method, and the controls

**One binary, both arms.** `OFF` is `AXEYUM_QINST_SKOLEM_PRIME=0`, `ON` is
`512`. Every comparison below is between two runs of the *same* executable, so
nothing here can be a compilation difference. The unpatched binary was also
swept, and reproduces both baselines exactly: 32-file slice **1/32**, 24-file
win list **24/24** (22 `sat`, 2 `unsat`).

**Inert at the shipped value.** The pass ships at `0`, so the claim that it
changes nothing is itself measured rather than argued from the early return.
A release binary built with `SKOLEM_PRIME_SHIPPED = 0`, run with **no
environment variable set at all**, reproduces the unpatched binary on the
population that showed the regression and on both files that matter:

| | unpatched | shipped default |
|---|---|---|
| 24-file win list | **24/24** (22 `sat`, 2 `unsat`) | **24/24** (22 `sat`, 2 `unsat`) |
| `Hoare/smtlib.1116374` (the one decided loss) | `unsat` | `unsat` |
| `Arrow_Order/uf.558544` (the file the ON arm loses) | `unsat` | `unsat` |

**Verdict diffs are keyed on the FILE PATH, never on row order.** An earlier
comparison in this session used `paste` across two sweep files of unequal length
and manufactured a gain and a loss that did not exist — the shifted rows read as
`f26` gaining and `f27` losing, and neither had changed. Every number below
comes from a path-keyed join that asserts the two populations are equal sets
before it compares anything.

**A sweep loss on a loaded box is not a finding until it is isolated.** The
24-file sweep showed two losses; re-running both, one after the other, on one
binary, gave one real regression and one load artefact. Reporting the sweep
number alone would have doubled the measured cost.

**The end-to-end unit test failed on its own vacuity guard, and that is
recorded.** The first version of the guard built a toy — two universals
contradicting through a Skolem application, plus a noise universal to keep
matching non-empty — and asserted `OFF` must not decide it. `OFF` decided it:
at that size the loop's other rungs already reach the shape. So **no toy can
discriminate the two arms on a verdict**, the corpus is the discriminator, and
the shipped test pins what the pass *produces* instead (the application at the
claimed arguments, nothing at budget `0`, and the instance passing the
certificate gate).

## The three deliverable observables

### 1. Do the previously-flooded files now report a nonzero `term-invention round` count?

**No.** Unchanged at zero.

| file | invention rounds, base | invention rounds, ON |
|---|---:|---:|
| f01 | 0 | 0 |
| f05 | 0 | 0 |
| f12 | 0 | 0 |
| f20 | 0 | 0 |
| f22 | 0 | 0 |

This is by construction, not a failure of the pass: priming does not go through
the invention route at all, and does not touch either of its gates. The flooded
files still flood to `ground=8192` and the 4096 ceiling still holds. Anyone
reading observable 1 as a proxy for "did the term get built" should read
observable 2 instead — they came apart here.

### 2. Is the required Skolem application present in the `AXEYUM_QGROUNDDUMP` output?

**Yes, and Q2's stated numeric observable moves.**

On `Hoare/uf.966336`, the file Q2 read completely:

| | OFF | ON |
|---|---|---|
| distinct `f18` applications | `(f18 f29 !q.?v2.7)` only | `(f18 f29 !q.?v2.7)` **plus** `(f18 f29 (!qskf_35 !sk_1 !sk_0))`, `(f18 f29 (!qskf_35 !sk_1 f12))`, `(f18 f29 (!qskf_35 !sk_1 f26))` |
| `!qskf_` applications at `!sk_0` | **0** | `(!qskf_35 !sk_1 !sk_0)` and others |

`!sk_0` is the goal's `S6` Skolem, which the goal asserts equal to
`(f19 (f20 f29) f28)`, so `(!qskf_35 !sk_1 !sk_0)` is z3's
`(?v2!0 (f19 (f20 f29) f28))` up to the congruence Q2 established from the goal
and the argument-reversal convention Q2 measured. Q2's condition — *"that second
count goes from 0 to ≥ 1"* — is **met**.

Across Q2's ten (i) files, counting **distinct fully-ground** `!qskf_`
applications in the dump (no `!q.` binder, no `!qu_` hoisted universal), OFF vs
ON on one binary:

| file | OFF | ON | dump rows OFF → ON | verdict OFF → ON |
|---|---:|---:|---|---|
| f10 `gram_lang/…1432776` | **0** | **229** | 11 024 → 10 642 | unknown → unknown |
| f12 `rbt_impl/…992499` | **0** | **210** | 19 327 → 23 764 | unknown → unknown |
| f19 `Arrow_Order/uf.813308` | 1 | **111** | 9 385 → 9 134 | unknown → unknown |
| f18 `Arrow_Order/uf.704291` | 6 | **215** | 14 050 → 15 598 | unknown → unknown |
| f06 `coinductive_list/…2500061` | 6 | **120** | 18 972 → 15 068 | unknown → unknown |
| f01 `bindag/…1094926` | 10 | **58** | 23 499 → 11 951 | unknown → unknown |
| f29 `Hoare/uf.966336` | 2 | **15** | 2 845 → 5 059 | unknown → unknown |
| f31 `TypeSafe/smtlib.1098821` | 512 | 532 | 2 468 → 2 502 | unknown → unknown |
| f28 `Hoare/uf.834137` | 22 | 22 | 16 392 → 16 620 | unknown → unknown |
| f17 `Arrow_Order/smtlib.663965` | 12 | 12 | 998 → 978 | unknown → unknown |

**Six of the ten move by an order of magnitude, two move a little (`f29` 2 → 15,
`f31` 512 → 532), two do not move at all, and none of the ten changes verdict.**
On `f17` and `f28` the pass finds no eligible universal it can seed beyond what is
already there — those are the files where "we never build it" is *not* explained
by this shape, and they are where a follow-up would look. `f31` already held 512
such applications with the pass off, which is its own comment on how far "the
term is absent" is from "the term is what is missing".

Note the dump-row column: on `f01` and `f06` the primed run's ground set is
**smaller**, not larger. The pass does not simply add traffic; it changes which
instances fill the cap. That is the same mechanism that costs `uf.558544` below.

### 3. Does the 32-file slice decide more than 1, with the 24 wins still at 24?

**No, and no.**

| population | arm | decided | PAR-2 (s) | gained | lost |
|---|---|---:|---:|---|---|
| 32 losses | OFF (= shipped) | **1/32** | 1500.3 | — | — |
| | ON (512) | **1/32** | 1500.5 | `[]` | `[]` |
| 24 wins | OFF (= shipped) | **24/24** | 20.4 | — | — |
| | ON (512) | **22/24** | 124.3 | `[]` | `Arrow_Order/uf.558544`, `TypeSafe/smtlib.1262852` |

No arm on either population produced a verdict contradicting a declared
`:status`; the contradictory-flip count is 0 on both.

Of the two losses, **one is real**:

| file | OFF, isolated | ON, isolated |
|---|---|---|
| `Arrow_Order/uf.558544` | **`unsat`, 3 615 ms** | **`unknown`, 22 235 ms** |
| `TypeSafe/smtlib.1262852` | `sat`, 10 522 ms | `sat`, 12 026 ms |

So the honest cost is **one refutation, not two** — and it is a refutation the
shipped code finds in 3.6 s, turned into a 24 s `unknown`. This is the
perturbation shape `qinst_egraph.rs` already records against itself at
line 5396 — *"a per-pattern split measurably perturbed the loop's admission
schedule and cost a scored refutation"*. Extra admitted instances change
*which* instances fill the caps, and a file whose refutation was cheap stops
being reachable.

## Verdict: DO NOT BUILD

Gain side **empty** on the population it was aimed at; cost side **one win**.
The pass is retained in the tree at `SKOLEM_PRIME_SHIPPED = 0`, with the
measurement written next to the constant, for the same reason `GroundBudget` is
an object rather than three `const`s: the next lane that wants to ask "is the
gap construction?" should be able to ask it in one environment variable rather
than in a patch, and should find this answer before spending the tokens.

## What this refutes, and what it hands the next lane

**Refuted: "the terms a refutation needs must be BUILT, not found" is not, on
this population, a sufficient diagnosis.** It is a true statement about the
ground set — Q2 measured that correctly, and this note confirms the terms really
were absent and really can be built cheaply. It is not a statement about the
verdict. Building them changed nothing.

**What that leaves.** Q2 was explicit that having the term is not sufficient,
and named four generation-0 (ii) files — `f14`, `f15`, `f22`, `f26` — where
every required term sits inside the first 1.2% of the ground set and the loop
still does not close. This measurement adds `f29` to that list and takes it off
the construction list. The (i)/(ii) split therefore moves in the direction that
makes **selection** the whole problem:

- Q2: (i) 10, (ii) 6 of 16 attributable.
- After this: the construction half of (i) is reachable on demand at negligible
  cost, and on the file measured end to end it is done.

The next question is not "how do we build the term" and not "how much budget"
— both are now bounded and both came back zero. It is **why an e-graph holding
the refuting instance's terms, with the instance itself admitted and
certificate-checked, does not produce a conflict**. That is a question about the
ground refutation check and the clause selection under it, not about
instantiation.

## What I did not measure

- **Whether a different priming budget avoids the `uf.558544` loss.** Not
  attempted. It could not change the verdict, because the gain side is empty at
  the arm that closed the construction gap most fully — tuning down can only
  build fewer terms.
- **The 14 files z3 also times out on.** Untouched, as in Q2.
- **`f23`** (z3 produces no proof) and the 6 (ii) files. Out of scope here.
- **`cargo test --workspace`, clippy over the whole workspace, and the string
  and arithmetic suites.** Out of this lane's scope; the gates that were run are
  listed below.
- **Whether the un-Skolemized rung (angle a) is worth removing on its own.**
  Not run. Q2 predicts a cost fix with no verdict movement and says so; nothing
  here bears on it.
- **cvc5.** Still not installed.

## Gates run

All on the tree carrying the pass at its shipped `0`, with a **nonzero test
count confirmed in each** — a feature-gated suite compiles to nothing and
exits 0.

| gate | result |
|---|---|
| `cargo test -p axeyum-solver --features full --test corpus_regression` | **2 passed**, 0 failed |
| `cargo test -p axeyum-solver --features full --test quant_skolem_egraph_routing` | **1 passed**, 0 failed |
| `cargo test -p axeyum-solver --lib --features full` | **1682 passed**, 0 failed |
| `cargo test -p axeyum-solver --test progress_frontier --features full -- --test-threads=1` (under `taskset -c 0-7`) | **12 passed**, 0 failed |

**The frontier run's own reference frame, read from the artifacts it wrote
rather than from the pass count** — the ratchet is only enforced on the families
it calls comparable, and on this busy box two were not:

| family | baseline | frontier | comparable / ratchetable |
|---|---:|---:|---|
| `bv_reduction` | 30 | 33 | yes |
| `lia_cuts` | 26 | 35 | yes |
| `nia_unsat` | 40 | 40 | yes |
| `nra_degree` | 40 | 40 | **no** — ratchet not enforced |
| `string_bound` | 8 | 40 | **no** — ratchet not enforced |

So the green on `nra_degree` and `string_bound` is **advisory**: it is not
evidence of no regression there, and no baseline may be raised from this run.
The three enforced families are at or above baseline. The pass is inert at its
shipped value, so a frontier regression from it would be surprising — but that
is an argument, and the two advisory rows are stated as unmeasured rather than
folded into "12 passed".

The four new unit tests were **mutation-checked**, not just run: replacing the
pass's seed lists with an empty map kills
`skolem_priming_builds_the_application_at_the_arguments_it_claims` and **exactly
that one** — the other three stay green. The mutant was applied and reverted in
this isolated worktree, never in the shared checkout.

## Reproducing

```sh
scripts/cargo-serialized.sh build --release -p axeyum-bench \
    --example axeyum_cli --features axeyum-solver/full

# the arm this note measured. THE SHIPPED DEFAULT IS 0, so an unset variable
# is the OFF arm and reproduces the unpatched binary.
AXEYUM_QINST_SKOLEM_PRIME=512 AXEYUM_QPROBE=1 \
  AXEYUM_QGROUNDDUMP=/tmp/f29.on.dump \
  ./target/release/examples/axeyum_cli \
  /nas3/.../UF/sledgehammer/Hoare/uf.966336.smt2 --timeout-ms 24000

# the control, same binary
AXEYUM_QINST_SKOLEM_PRIME=0 AXEYUM_QGROUNDDUMP=/tmp/f29.off.dump \
  ./target/release/examples/axeyum_cli \
  /nas3/.../UF/sledgehammer/Hoare/uf.966336.smt2 --timeout-ms 24000

# the observable, on each dump
grep -o '(f18 f29 ([^()]*))' /tmp/f29.on.dump | sort -u    # 3 rows
grep -o '(f18 f29 ([^()]*))' /tmp/f29.off.dump | sort -u    # none

# distinct fully-ground Skolem-function applications
grep -oE '\(!qskf_[0-9]+ [^()]*\)' <dump> | grep -v '!q\.' | grep -v '!qu_' \
  | sort -u | wc -l
```

The sweep harness, the path-keyed verdict differ and the census script live in
this session's scratchpad and are not committed; the committed artifacts are the
pass itself and its tests. `AXEYUM_QGROUNDDUMP` was landed by Q2 (`f87d0f649`).
