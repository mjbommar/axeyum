# Lane: zero-inst — the refutation was available before instantiating, and we dropped the assertion carrying it

<!-- plan-section: lane-status -->

**Lane zero-inst (`DONE`, zero-inst, 2026-09-14).** [ADR-2020] measured that
cvc5 refutes nine of our skeleton-refusal files with **zero instantiation
tuples** and left the follow-up open. This lane answered it and shipped the
lever it pointed at: **+9 of 129 rows, the first net gain on this gap after six
consecutive closed hypotheses.** Full reasoning in [ADR-2025]; artifacts in
[`bench-results/zero-inst-20260914/`](../../../bench-results/zero-inst-20260914/PREREGISTRATION.md).

## What actually refutes those nine files

The obvious hypothesis is **false**. The ground assertions alone are **`sat`**
on 8 of the 9 (cvc5 and z3 agreeing), so the quantifier-free part is not
contradictory. On **9 of 9**, exactly **one** assertion — always the **last**,
the negated verification condition, 1 of 589 — is unsat **on its own**, and
cvc5 still refutes it with every quantifier module disabled and again with
`--simplification=none`.

Measured on the **benchmark** rather than on cvc5: replacing every maximal
quantified subformula by one opaque atom leaves a **quantifier-free skeleton
that is already unsat** on 8 of 9, confirmed by two independent solvers. The
9th has a **`sat`** skeleton, which is what makes the probe non-vacuous.

## We have this check — twice — and neither can fire

`ground_subset_refutes_quantified_query` (`auto.rs:162/767`) and a round-0
check inside the loop (`qinst_egraph.rs:2386`) both **DROP** whole conjuncts
that *contain* a quantifier. Neither **abstracts** a quantified *subformula*.
The refutation lives inside one assertion and that assertion contains
quantifiers, so dropping it throws the refutation away. **This was measured
before the code was read** — the ground part being `sat` is exactly the verdict
that makes the existing rung correctly decline.

`exceeds_pre_sat_skeleton_boundary` is **not** this, despite the name: it is a
size admission bound downstream of instantiation that never returns `unsat`.

## The transferable number is 11.6 %, not 89 %

The 8/9 is a rate on a population **selected by its outcome** (R3). On the whole
129-row winnable population the skeleton is unsat on **15**, 11.6 %
`[7.2 %, 18.3 %]`, with **12 reported NOT MEASURED** (their quantifiers live in
`define-fun` bodies, which the diagnostic refuses to abstract because a constant
cannot track a parameter). All 15 agree across five columns: declared `:status`,
z3, cvc5, the shared-atom skeleton, and a **fresh-per-occurrence** skeleton
added as a soundness control because text-level atom sharing is not
unconditionally sound under `let`.

## The lever, and the A/B

`q:bool-skeleton` abstracts instead of dropping. Interleaved per file, one
binary two env values, s5 `{1,3,5}` + s6 `{1,3,5}` held fixed across every
phase, 24 s budget.

| run | rows | GAIN | LOSS | FLIP | wall |
|---|---:|---:|---:|---:|---|
| **main** `UFLIA`+`UFNIA` | 129 | **+9** `[3.7 %, 12.7 %]` | 0 | 0 | **0.93x** |
| **noise floor** (both arms shipped) | 129 | 0 `[0.0 %, 2.9 %]` | 0 | 0 | 1.00x |
| control `QF_BV` | 6 | 0 | 0 | 0 | 1.00x |
| control `AUFLIA` | 30 | 0 | 0 | 0 | 1.01x |

All nine carry `rung=decided` in the route trail. **R5: 9 of 9 STABLE-GAIN**
over three passes per arm. **R9: 0 disagreements at a full 9/9 comparable
denominator** on each of `:status`, z3 and cvc5. The `AUFLIA` control is the one
that carries weight — the rung **fired** on one row there and agreed with the
off arm — whereas `QF_BV` is weak and said to be (the rung is absent, since
quantifier-free queries never enter the ladder).

**Ships ON**, so `AXEYUM_ZERO_INST_SKELETON` inverts to a **kill switch**. The
shipped default is **verified, not predicted**: a fresh release binary with no
environment variable decides 9/9, and the kill switch reverts 9/9.

## Why only 9 of 15, and where to look next

**4 RUNG-NEVER-REACHED** (the ladder stops at `fd:parse`; all `UFNIA`),
**2 CAPABILITY-LIMIT** (the rung runs and declines at both 24 s and 5x it — our
ground checker cannot refute a skeleton cvc5 *and* z3 both refute), and
**0 BUDGET-LIMIT**. The zero says the probe's one-tenth share is not what binds,
so raising it buys nothing.

The two open axes: **dispatch** (why 4 files never reach the quantified ladder —
no ADR in this series has looked at it) and the **ground checker** itself, now
stated in its cleanest form — a quantifier-free query two independent solvers
refute and we cannot, with no quantifiers, no instantiation and no admission
bound in the way.

[ADR-2020]: ../../research/09-decisions/adr-2020-the-ground-checker-mostly-refuses-and-the-set-it-refuses-is-one-we-had-no-need-to-build.md
[ADR-2025]: ../../research/09-decisions/adr-2025-the-refutation-was-available-before-instantiating-and-we-dropped-the-assertion-carrying-it.md

<!-- plan-section: landed-changes -->

| 2026-09-14 | zero-inst | [ADR-2020] measured that cvc5 refutes nine of our skeleton-refusal files with **ZERO instantiation tuples** and left the follow-up open. Answered, and the answer **inverts the obvious hypothesis**: the GROUND assertions alone are **`sat`** on 8 of the 9 (cvc5 and z3 agreeing), so "the quantifier-free part is already contradictory" is FALSE. On 9 of 9 exactly **one** assertion — always the LAST, the negated verification condition, **1 of 589** — is unsat **on its own**, and cvc5 still refutes it with every quantifier module disabled AND with `--simplification=none`. Measured on the BENCHMARK rather than on cvc5: replacing every maximal quantified subformula by one opaque atom leaves a **quantifier-free skeleton that is already unsat** on 8 of 9, confirmed by two independent solvers (the 9th is `sat`, which is what makes the probe non-vacuous). **We have this check — twice — and neither can fire**: `ground_subset_refutes_quantified_query` (`auto.rs:162/767`) and the round-0 check (`qinst_egraph.rs:2386`) both **DROP** whole conjuncts that CONTAIN a quantifier, while the refutation lives INSIDE one; this was measured before the code was read. Widened to the 129, the skeleton is unsat on **15**, **11.6 % `[7.2 %, 18.3 %]`** — NOT the 8/9 of the seed, a population selected by its outcome (R3) — with **12 reported NOT MEASURED** (quantifiers inside `define-fun` bodies; R15's liveness exit fired) and all 15 agreeing across `:status`, z3, cvc5, the shared-atom skeleton and a **fresh-per-occurrence** skeleton added because text-level sharing is not unconditionally sound under `let`. A new **`q:bool-skeleton`** rung that ABSTRACTS instead of dropping moves **+9 of 129, 0 losses, 0 flips**, every gain carrying `decided` in its route trail, **9 of 9 STABLE-GAIN** over three passes per arm, **0 disagreements at a full 9/9 comparable denominator** on each of three authorities, against a same-arm noise floor of **0 of 129** and at **0.93x** wall. Controls: `QF_BV` 0 (weak, and said to be — rung ABSENT) and **`AUFLIA` 0 with the rung FIRING on one row and agreeing**. **SHIPS ON**, so the env var inverts to a KILL SWITCH — and the shipped default is **verified** (9/9 decided with no environment variable, 9/9 reverted under the kill switch), not predicted. `mutation_controls.py` reported the liveness floor **SURVIVED** and the maximality anchor **AMBIGUOUS** on its first run; both were fixed and all three guards now kill **exactly one** test each. Of the 15, the 6 that did not convert split **4 RUNG-NEVER-REACHED / 2 CAPABILITY-LIMIT / 0 BUDGET-LIMIT** — the zero says the probe's one-tenth share is not what binds. Three instruments lied in flight and were fixed: **499 of 589 singleton probes counted as `errors` were `sat` verdicts** (the benchmark's own `:status` turns a correct `sat` on a subset into `(error …)`), both mechanism columns of the first strategy isolation read `NONE` because cvc5 **REFUSES** `--opt=false` and wants `--no-opt`, and a 107 ms timing column was fork overhead around an **11 ms** solve. | ADR-2025 |
