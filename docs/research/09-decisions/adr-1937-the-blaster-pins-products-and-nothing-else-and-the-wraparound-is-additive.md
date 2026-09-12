# ADR-1937: The blaster pinned products and nothing else, and the wraparound was additive

Status: accepted
Index-summary: ADR-1921 closed the QF_NIA width lead (escalating to 64 decides **0 of 110**) and left one hypothesis standing, explicitly unmeasured: `blast_integers` emits a no-overflow constraint for `int_mul` and for **nothing else**, so the replay failures that survive must be ADDITIVE wraparound. Measured, it is right. The analogous constraint on `int_add`/`int_sub`/`int_neg` takes QF_NIA from **39 decided to 78** over the whole 200-file division — 40 gains, 0 real losses, 0 verdict flips — and it is **10.2 % FASTER**, because a constrained search stops wandering through wrapping models the replay would reject anyway. Cost on 298 already-decided files across nine integer-bearing divisions: 0 real losses, 0 flips, +1.9 % wall. 78 verdicts against `:status`, z3 and cvc5: **0 disagreements** (checker verified able to fail: 78 under a flip control). It ships ON, with `AXEYUM_INT_BLAST_ADDITIVE_NO_OVERFLOW=0` to A/B it back off. Two negatives land with it: the re-census of all 110 winnable files shows the ADR-1925 relabel hid **nothing** in this division (unlike QF_NRA), and the largest honest class — the width ladder's wall clock, 41 of 110 — decides **1 of 41 at 6.25x the budget**, so it is not a clock problem either.
Index-status: accepted
Date: 2026-09-12

## Context

QF_NIA is the largest single-division gap on the 2026-09-11/12 head-to-head
board: axeyum 41 of 200, z3 144, cvc5 87, **110 winnable**, gap **+103**.

Two leads were already closed by measurement before this lane started, and
neither is reopened here:

- **Bounded-integer width escalation** ([ADR-1921](adr-1921-the-int-blast-width-escalation-is-measured-and-not-shipped.md)):
  decides 0 of 110, costs +4.6 % wall, and replaces 23 precise
  `overflowed at width 32` diagnoses with uninformative timeouts. At 150 s it
  decides 3 of 23, and the **baseline at the same 150 s decides the same three
  files with the same verdicts**, so the escalation contributed nothing.
- **CNF clause budget** (`docs/plan/notes/118-nia-diagnosis.md`): lifting it by
  the estimator's own measured 9.4x over-approximation decides 0 of 49.

ADR-1921 closed with one sentence marked as a hypothesis and not a result:

> the blaster constrains **`int_mul`** against overflow and nothing else, so the
> replay failures that survive are additive wraparound. An additive no-overflow
> constraint is sound by the same argument as the multiplicative one. Unmeasured.

This ADR measures it.

## Step 0 — the census had to be re-run first, and the answer was "nothing was hiding"

[ADR-1925](adr-1925-an-engine-internal-unsupported-is-a-decline-and-a-relabel-must-carry-what-it-replaces.md)
established that `preprocessed dispatch timeout after reduced solve` is a
**relabel**: `dispatch_reduced` replaced the reduced solve's own reason instead
of carrying it. In QF_NRA that one sentence covered 18 files and **13 of the 18
were really the CAD wall**. It was the top class of the QF_NIA census too, at 41
of 110, so every QF_NIA number rested on a string that carried no cause.

Re-censused on current main, all 110 winnable files (not a sample), with the
carrier decomposed:
[`bench-results/qf-nia-dispatch-20260912/`](../../../bench-results/qf-nia-dispatch-20260912/README.md).

| honest cause | files | share |
|---|---:|---:|
| `integer bit-blast width ladder: wall-clock timeout reached` | **41** | 37 % |
| `estimated N CNF clauses before lowering exceeds budget N` | 31 | 28 % |
| `bounded integer model overflowed at width 32 … widen the bound` | 25 | 23 % |
| watchdog fired before the worker thread returned | 6 | 5 % |
| `combined-theory timeout after scalar backend` | 3 | 3 % |
| `integer constant does not fit the bounded width 32` | 2 | 2 % |
| `distinct` pairwise-expansion ingest limit | 1 | 1 % |
| `no model within the bounded integer width 32` (in-range `unsat`) | 1 | 1 % |

**The QF_NRA finding does not repeat here.** All 44 carrier rows decompose into
the same bit-blast route the census already named — 41 say the width ladder ran
out of wall clock, 3 say the scalar backend did. The relabel cost QF_NIA its
precision, not its diagnosis. That is worth recording as a result rather than
skipped as a null: a general rule ("a relabel hides a different cause") held in
one division and did not in the next, and the only way to know which is to run it.

Two method points the old census could not make:

- **The dispatch ran to the END.** A pure-integer query's trail is 19 rungs
  (`fd:parse`, `probe`, `dl-online`, `lia-simplex`, `lia-dpll`, `nia-square`,
  `int-real-relax`, `nia-linearize`, `nia-bounded-blast`, `int-blast-ladder`,
  then 9 string front-door wrappers declining on budget). 103 of 110 ran 19–22
  attempts. The two exceptions are themselves findings: 6 watchdog kills have no
  route line, and 1 file is refused at ingest (`attempts=1`).
- **What refused and what spent the clock are different routes on 49 of 110.**
  `nia-linearize` is `bound_by` on 49, and on 30 of those the verdict that ends
  the file is an *instantaneous* pre-lowering CNF estimate refusal — the
  linearizer burned most of a 24 s budget for a refusal available in the first
  second.

## Step 1 — the largest honest class is not a clock problem either

The 41 `ladder-clock` files re-run at **150 s** (6.25x the competition budget,
hard wall 260 s): **1 of 41 decided** (`sat`, 58.5 s). At six times the budget
the class also decomposes further — 13 become the CNF-clause refusal, 10 the
watchdog, 4 the width-32 replay overflow, 3 the scalar-backend clock, and only
10 are still the ladder's clock.

So "give the ladder more budget" is a measured negative, and that is what closed
the obvious reading of the largest class. Data:
`deep-ladder-clock-150s.tsv`.

## Decision

**Emit a no-overflow side-constraint for `int_add`, `int_sub` and `int_neg`, the
way `blast_integers` already does for `int_mul`, and ship it ON.**

- `Blaster::additive_no_overflow_constraint` sign-extends each operand by **one
  bit** (a signed sum, difference or negation of `B`-bit values always fits in
  `B+1`), recomputes the operation there, and requires it to equal the
  sign-extension of the width-`B` result. That holds iff the width-`B` operation
  did not wrap.
- `int_neg` is in the arm deliberately: `-MIN` wraps to itself, and no
  `add`/`sub` constraint catches it.
- `ADDITIVE_NO_OVERFLOW` ships `1`; `AXEYUM_INT_BLAST_ADDITIVE_NO_OVERFLOW=0`
  restores the pre-ADR-1937 encoding for an A/B, and the entry is registered in
  `config_registry` so it appears in `--trace`'s `; config` line.
- `blast_integers_with_additive_no_overflow` takes the flag as an **argument**.
  The lever resolves once per process through a `OnceLock` and `unsafe_code` is
  denied workspace-wide, so a test cannot set the variable at all — an
  explicit-flag entry point is what makes the armed behaviour testable rather
  than a gate on one shell.

### What is NOT covered, stated rather than inferred

`IntAbs`, and the `bv_add`/`bv_sub` inside the Euclidean `IntDiv`/`IntMod`
construction, are built in `build_int_app` rather than in the constrained arm
and get no constraint. Extending to them is a separate measurement.

## Evidence

Full data: [`bench-results/qf-nia-dispatch-20260912/`](../../../bench-results/qf-nia-dispatch-20260912/README.md).
One release binary, both arms, arm order alternating per file, both arms of a
file run back to back inside one worker so the pair shares ambient load. Three
workers on s4 pinned to cores 8–15, under concurrent lane load.

### The whole QF_NIA division (200 board rows, 201 paths)

| | baseline (arm A) | armed (arm B) |
|---|---:|---:|
| decided | **39** | **78** |
| gains | — | **40** |
| losses | — | 1 raw, **0 after re-check** |
| `sat`/`unsat` disagreements between arms | — | **0** |
| wall total | 3,607 s | 3,239 s (**−10.2 %**) |
| both-decided wall ratio | — | 0.995 |

**It is faster, not slower.** That is the shape the mechanism predicts: the
constraint removes the wrapping models the exact-integer replay was going to
reject anyway, so the search stops paying for them.

### Every single-pairing surprise was re-run, and every one was a load flake

Four surprises came out of the two parallel A/Bs. All four were re-run serially,
pinned to cores 0–7, arms back to back, nothing else of this lane's running.
**All four reproduce identically in both arms**, so the treatment has 0 real
losses:

| file | parallel A/B | serial re-check (both arms) |
|---|---|---|
| `From_T2__n-7.t2_fixed__p4922…` (QF_NIA) | A `unsat` 6.7 s / B `unknown` 24.3 s | `unsat` 6.3 s / `unsat` 6.3 s, 4 of 4 |
| `xy.12.x.12.r.3…gph` (QF_IDL) | A `sat` 19.2 s / B `unknown` | `sat` ≈9.8 s both arms, 3 of 3 |
| `ex8280_2400_100` (QF_LIA) | A `sat` 18.8 s / B `unknown` | `sat` 16.9 s both arms, 3 of 3 |
| `hash_uns_04_20` (QF_UFLIA) | A `unsat` 15.8 s / B `unknown` | `unsat` 8.6 s both arms, 3 of 3 |

Three gains were re-checked the same way and all reproduce: `LessLeaves…p10018`
(A `unknown` 24.1 s, B `sat` 15.1 s, 3 of 3), `fun1.t2_fixed…p697` (A `unknown`
24.6 s, B `sat` 15.4 s, 2 of 2), `SAT14/571` (A `unknown` 24.9 s, B `sat` 7.6 s,
2 of 2).

**Both the raw and the re-checked numbers are reported** because a 16 s baseline
against a 24 s budget flips under ambient load, and this repository has already
published one false convert from exactly that.

### Against the board, not only against the arm

The board's own baseline for this division is 41; this host's baseline arm
reproduced **39** of those 41 under three-way load. The two it missed —
`919.smt2` and `From_T2__n-21.t2__p3959…` — are host/load effects, not treatment
effects: `n-21` was missed by **both** arms and decides `unsat` in 8.3 s in both
arms when re-run serially. So on equal footing the division goes

> **41 → 80 of 200** (78 measured in the armed arm, plus `n-21` and `n-7`, each
> verified serially in both arms),

which closes **39 of the 103-file gap** to z3's 144.

### Cost to what already works

298 already-decided files, sampled every fourth from the nine integer-bearing
divisions (QF_LIA, QF_UFLIA, QF_IDL, QF_RDL, QF_NRA, QF_ABV, QF_SLIA, QF_DT, UF):

| | |
|---|---:|
| baseline decided / armed decided | 290 / 289 |
| real losses (after serial re-check) | **0** |
| verdict flips | **0** |
| wall | **+1.9 %** (both-decided ratio 1.027) |

The sample **resolves before it samples**: sampling first and dropping what will
not resolve made QF_LIA's contribution 7 files instead of 27, because 92 of its
119 decided rows share a basename with another corpus directory and the board
cannot say which one it ran. QF_LIA is the division an additive constraint taxes
most, so a sample size decided by basename collisions would have been the wrong
measurement of the wrong thing.

### Soundness

**78 verdicts** — every file the armed arm decided, not only the 40 gains —
cross-checked against three independent authorities keyed by full path: the
benchmark's own `(set-info :status …)`, `z3 -T:60`, and
`cvc5 --tlimit 60000` (the units differ, which is why they are written out).

> **78 verdicts, 0 disagreements, 0 verdicts with no authority.**

The checker was verified able to fail: inverting every verdict yields **78**
disagreements, so the zero is a measurement and not a checker that cannot speak.

## Why the constraint cannot produce a wrong verdict

It is a **restriction** at width `B`: it can only shrink the bit-vector model
set.

- `Sat` stays anchored by the exact-integer replay in `lia.rs` / `combined.rs`,
  which re-checks every original assertion under the ground evaluator regardless
  of how the model was found.
- A bit-vector `Unsat` with integers present is already reported as `unknown`
  ("no model within the bounded integer width"), never as an integer `unsat`.
- So a mis-encoded constraint can only make the search MISS a model — a wider
  rung, or a sound `Unknown` — never accept a wrong `Sat`.

**The one place a bit-vector `Unsat` IS trusted** is
`auto::solve_exact_bounded_box`, which re-blasts a box-clamped query and
transfers the raw refutation. This is named rather than left to be inferred,
because it is the only place the argument above does not already cover. It is
safe: `BoundedBox::width` is proven to cover **every Int subterm's** interval,
not merely every variable's, so at that width no operation wraps and these
constraints are *implied* — they cannot remove a model that route could
otherwise have found. The pre-existing `int_mul` constraint has rested on the
same property since it shipped. The 499 paired solves produced **0 verdict
flips**, which is the empirical half of the same statement. If this is ever
revisited, that function is where to look.

## How each guard can fail

Four mutations, each removing exactly one part of the encoding, through
`scripts/tests/mutation_controls.py int-blast-additive-no-overflow`
(baseline green, 10 tests):

| mutation | result |
|---|---|
| the constraint compares the widened result against **itself** (a counted tautology) | `killed 2` |
| extends by **zero** instead of by sign | `killed 2` |
| `int_neg` leaves the constrained arm | **`killed 1`** |
| the lever ships OFF instead of ON | **`killed 1`** |

Nothing survives. The two that kill two both kill the same pair — the width-4
enumeration and the `-MIN` test — because those are the two tests that assert
*exclusion*, and a tautological constraint excludes nothing. That is the
encoding being one function, not guards routing through one shared check; the
count tests stay green under both, which is exactly why the enumeration exists.

The soundness-negative is
[`crates/axeyum-solver/tests/additive_no_overflow_never_becomes_unsat.rs`](../../../crates/axeyum-solver/tests/additive_no_overflow_never_becomes_unsat.rs),
and it is two tests because either alone is worthless:

1. the hazard is **real** — the armed encoding refutes, at width 6, a query
   satisfiable over the integers (`x > 20 ∧ y > 20 ∧ x + y ≠ 0`), and the unarmed
   encoding does not;
2. the consumer **never transfers** such a refutation — deleting the
   `has_integers` arm in `combined.rs` makes it answer `unsat` to a satisfiable
   query.

A "never transfers" test over a refutation nothing produces cannot fail.

## Gates run

`cargo check --workspace --all-targets`; `clippy --workspace --all-targets
--all-features -D warnings`; `cargo fmt --all --check`; `axeyum-rewrite --lib`
(164 passed); `axeyum-solver --lib --features full -- --test-threads=4` (**1718
passed**); `--test corpus_regression` (2); `--test progress_frontier --features
full -- --test-threads=1` (**12 passed**); the four string front-door suites
(2 / 48 / 82 / 13) and the new soundness-negative (13, and 2 in its own binary).
Every one asserted by its `test result:` line and a nonzero count.

## Consequences

- QF_NIA's **width family is now a fixed class, not a lead**: ADR-1921 closed
  widening, and this closes what widening was standing in for. The 25
  `replay-overflow` files and a large share of the ladder-clock 41 are decided by
  one side-constraint.
- **ADR-1921 stays correct and its hypothesis is now a result.** Nothing in it is
  retracted: escalating the width still decides 0 of 110. The reason it decides 0
  is in this ADR.
- The two classes still standing after this are the **CNF clause budget** (31,
  already a measured negative on lifting the gate) and **`nia-linearize`
  consuming a budget it then cannot use** — it is `bound_by` on 49 of 110 files
  while 30 of those end in an instantaneous size refusal. That is the next
  QF_NIA lead, and it is a *scheduling* question, not a capability one.
- Revisit if `solve_exact_bounded_box` ever transfers a refutation at a width
  that does not cover every Int subterm, which is the one property the soundness
  argument rests on.
