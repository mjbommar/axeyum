# ADR-2136: order and monotonicity lemmas for QF_NIA — built, valid, and measured

Status: proposed
Index-summary: ADR-2112 Part E measured ORDER and MONOTONICITY lemmas ABSENT from `nia_linearize.rs` and its z3 ablation said no absent class is load-bearing on more than 3 of the 75 files z3 decides — a statement about z3's portfolio of seven, not ours of four. This builds both behind one dated lever shipped DISARMED and measures them on OURS. **SIZING first**, all 116 undecided QF_NIA T1 rows, 0 errored: the order lemma's step is available on **111**, monotonicity's on **115**, with a median **2,249** shared-factor product pairs per file and a max of **9,407,886** — so emission must be model-driven and capped, as z3's is. `unbounded_products` equals `products` at every quantile, which is why arming also has to widen `RefinementSetup::refine`: the entailed-bound passes produce nothing here, so without it the loop runs ONE round and the pass is unreachable. **REACHABILITY**, measured rather than assumed: the pass runs on **59 of 116** rows; the other 67 never produce a spurious model because the linear relaxation itself times out, so the ceiling on this population is the RELAXATION, not the lemma. **A/B**, one binary two env values, interleaved per file, 24 s/8 GiB, four populations at full 200/200 coverage: QF_NIA 82→80, QF_NRA control 124→124 (0 movers, as a Real-sorted control must), UFNIA **54→61**, held-out QF_NIA 85→85. **DISAGREEMENTS 0 of 800.** 15 raw movers re-checked 3x per arm: **10 STABLE-GAIN, 3 STABLE-LOSS, 2 UNSTABLE** — seven of the gains in UFNIA alone. **SHIPS DISARMED**: the criterion was 0 stable losses on pinned AND held-out, and there are 2 and 1. All three losses are `unsat → unknown` — budget starvation of a later ladder route, a SCHEDULING cost and not a lemma defect, which is the next lane's one-line experiment. Mutation: 2 mutations, both measured, killing 5 and 2, kill sets DIFFERENT, the soundness-negative fixture in the first. NOT RUN: all six z3 NIA differential fuzzes.
Index-status: proposed
Date: 2026-09-16

## Context

[ADR-2112] Part E inventoried our nonlinear-integer lemma portfolio against
z3's by the STEP each lemma takes rather than by its name, and found two
classes **absent** from `crates/axeyum-solver/src/nia_linearize.rs`:

- **order lemmas** — `nla_order_lemmas.cpp:286-310`, four sign-case
  implications coupling two monomials that share a factor;
- **monotonicity lemmas** — `nla_monotone_lemmas.cpp:61-90`, magnitude cuts
  taken at the current model assignment with no static bound.

Its Part D then measured, by **ablation on z3 itself**, that no single lemma
class is load-bearing for z3 on ≥ 15 of the 75 files z3 decides: the largest
is `nlsat` at 5, and the two classes above score 3 and — pooled with the rest —
no more. 66 of 75 files decide under every single-class removal. On that
evidence [ADR-2112]'s decision 4 says: do not build a single nonlinear lemma
class.

**That measurement is about z3's portfolio, not ours.** It says these classes
are redundant *for a solver that already has seven others*. Our portfolio has
four (sign, monomial bounds/McCormick, narrow-factor split, tangent), one of
which — the magnitude coupling — is conditioned on a static bound this
population does not have. So the open question [ADR-2112] did not answer is
what the two absent classes are worth **to us**, and answering it is a
measurement, not an argument.

Evidence, every script and per-row list:
[`bench-results/nia-order-lemmas-20260916/`](../../../bench-results/nia-order-lemmas-20260916/README.md).

## Part A — the sizing: is the step even available?

Before any code. `census_shared_factor.py` over all 116 undecided `QF_NIA` T1
rows (`bench-results/nia-trace-20260915/undecided-116.txt`), **116 files, 0
errored**, with applicability defined by the step each lemma takes:

| | files of 116 |
|---|---:|
| **order lemma applicable** (≥ 1 shared-factor product pair) | **111** |
| **monotonicity applicable** (≥ 1 product with an unbounded factor) | **115** |
| both | 111 |
| neither | 1 |

| per-file shape | min | median | p90 | max |
|---|---:|---:|---:|---:|
| nonlinear products | 0 | 242 | 1,911 | 38,472 |
| operands shared by ≥ 2 products | 0 | 53 | 239 | 2,924 |
| shared-factor product PAIRS | 0 | **2,249** | 44,415 | **9,407,886** |
| products with an unbounded factor | 0 | 242 | 1,911 | 38,472 |

Two numbers decided the design. Applicability is near-total, so neither class
is structurally inapplicable here — a live possibility, since 42 of these 116
never reach `cas-ideal-refuter` at all. And the candidate set is enormous, so a
static enumeration is out: emission has to be **model-driven and capped**,
which is also what z3 does.

The third number is the one that changed the plumbing: **`unbounded_products`
equals `products` at every quantile**. No product on this population has both
factors two-sidedly bounded, so `mccormick_lemmas` and `small_domain_lemmas`
produce nothing, and `RefinementSetup::refine` — which gates the whole
refinement loop on those having produced something — is false. Without a
change there, the loop runs ONE round on exactly the files this lane is aimed
at and the new pass is unreachable. See §C.

Controls: 8 fixtures, the census refuses to run if one fails, and an
independent check against the engine's own count — on the 89 rows carrying a
`nonlinear abstraction: N cross-products` detail (`nra.rs:567`, computed on the
normalized polynomial), both counts are nonzero on 89 of 89, 0 disagreements,
ratio median 1.00. The first join of those two files matched **0 rows** because
one path is corpus-relative and the other absolute; an empty overlap reads
exactly like total disagreement.

## Part B — the design claims, at `file:line` on all three sides

| step | z3 | cvc5 | ours (after this ADR) |
|---|---|---|---|
| order: couple two products sharing a factor | `nla_order_lemmas.cpp::generate_ol` `:286-310`, selected at the model by `order_lemma_on_ac_and_bc_and_factors` `:322-341`; the equality case `generate_ol_eq` `:265-284` | `monomial_bounds_check.cpp:308-325` — multiply an asserted inequality through by a term of known model sign, REVERSING the relation when that sign is negative (`infer_type`, `:308`); gated on the inferred fact being false at the current abstract model (`:317`) | `order_lemma_at_model`, `order_eq_lemma_at_model` |
| monotonicity: magnitude cuts at the assignment | `nla_monotone_lemmas.cpp::monotonicity_lemma_lt` `:80-90`, `::monotonicity_lemma_gt` `:61-72`, dispatched by `::monotonicity_lemma(monic const&)` `:23-39` | `monomial_check.cpp::checkMagnitude` `:193`, ordering monomials by the ABSOLUTE value of their abstract model values (`assignOrderIds(..., isAbsolute=true)`, `:202`) and emitting through `compareMonomial` `:517` | `monotone_lemmas_at_model` |
| magnitude atom without an `abs` term | `nla_basics_lemmas.cpp::negate_strict_sign` `:202-216` — replace the magnitude atom by a STRICT SIGN literal keyed off the current value's sign | — | the same: plain linear atoms against integer constants read from the model |
| tangent planes (already present) | `nla_tangent_lemmas.cpp` | `tangent_plane_check.cpp:37` | `tangent_lemmas` (`nia_linearize.rs:1732`) |

### B1 — why no `abs` term is needed, stated as the soundness argument

[ADR-2112] E1 noted that `nia_linearize.rs` contains **no IR magnitude term at
all**, and that both absent classes are stated on `|·|`. z3 does not build one
either, and the reason is not an encoding trick: the hypothesis literals it
emits pin the SIGN as well as the magnitude, so the product's sign is
determined and the two-sided `|m| ≥ |p|` collapses to a one-sided linear
comparison. Concretely, for `r ≈ a·b` at model values `(a_val, b_val)` with
`p = a_val·b_val` and neither factor zero:

```text
|r| too SMALL:  (a_val<0 ? a ≤ a_val : a ≥ a_val)
              ∧ (b_val<0 ? b ≤ b_val : b ≥ b_val)   →  (p<0 ? r ≤ p : r ≥ p)

|r| too LARGE:  (a_val<0 ? a_val ≤ a ≤ 0 : 0 ≤ a ≤ a_val)
              ∧ (b_val<0 ? b_val ≤ b ≤ 0 : 0 ≤ b ≤ b_val)
                                                     →  (p>0 ? r ≤ p : r ≥ p)
```

The second half of each `gt` hypothesis — the `a ≤ 0` / `0 ≤ a` — is the sign
pin, and it is not decoration. `monotone_gt_without_the_sign_pin_is_refutable`
constructs the weakened lemma by hand and shows the validity checker refutes
it: without the pin the hypothesis admits a factor of the opposite sign and
unbounded magnitude, and the conclusion is false there.

The order lemma's four cases collapse the same way. With `rac` and `rbc` the
abstraction variables for `a·c` and `b·c`:

```text
c > 0 ∧ ac ≥ bc → a ≥ b        c < 0 ∧ ac ≥ bc → a ≤ b
c > 0 ∧ ac ≤ bc → a ≤ b        c < 0 ∧ ac ≤ bc → a ≥ b
```

— the sign of `c`'s model value picks the first hypothesis, the relation the
model exhibits between the two ABSTRACTION values picks the second (not between
the products: the whole point is that the relaxation's `r` need not equal
`a·c`), and the lemma is emitted only when the model violates the conclusion.
`c = 0` emits nothing; `rac = rbc` is the equality case `c ≠ 0 ∧ ac = bc → a = b`,
which the four ordered implications structurally cannot reach.

**Every lemma is a consequence of `r = a·b` alone.** It is therefore true in
every integer model of the ORIGINAL query, exactly like the sign and tangent
lemmas: adding it can only shrink the relaxation's model space, an `unsat`
still transfers, and a `sat` is still accepted only after `replay_sat` against
the original assertions.

## Part C — what arming changes beyond the lemmas

`RefinementSetup::refine` gates the refinement loop on `mccormick + splits > 0`,
and §A measured that this population produces neither. Arming therefore also
widens that predicate:

```rust
refine: mccormick + splits > 0 || (order_lemmas && !rewritten_triples.is_empty()),
```

This is a real behavioural change and it is named here rather than buried: the
order and monotonicity lemmas need no static bound at all — that is
[ADR-2112] E1's second design claim — so on an armed run a product is itself
structure for a lemma to bite on. It also grants the loop the larger budget
slice `refine` selects. Both are behind the lever.

## Part C1 — the arm is wired, and it also RUNS

Two different claims, and only the first is usually checked. **Wired**:
`AXEYUM_NIA_ORDER_LEMMAS=notanumber` makes `config_lever.rs:124` panic, which
is [ADR-2112]'s own method — a lever proved by a panic rather than by a null
result. That proves the lever is READ and nothing more.

**Runs**: `reachability.sh`, all 116 undecided rows, armed arm, 24 s / 8 GiB,
0 dropped, every file classified from its trace rather than from its verdict.

| | files of 116 |
|---|---:|
| round 0 returned a spurious `sat` — the only way into the refinement loop | 47 |
| round 0 returned `unknown` — the relaxation itself ran out of budget | 67 |
| no round-0 line at all (parse fallback) | 2 |
| **built ≥ 1 order or monotonicity lemma** | **59 (50.9 %)** |

Lemmas built per reached file: 21 / **76** / 603 (min/median/max) over 3 / 13 /
47 refinement rounds.

**The ceiling here is the relaxation, not the lemma.** 67 files never produce a
spurious model to cut, because the linear DPLL(T) cannot solve the relaxation
inside its slice. That is a different problem from this lane's, and it bounds
everything in Part D: a lemma class cannot decide a file whose relaxation never
returns.

One file is decided by the armed arm in that single-arm probe —
`QF_NIA/UltimateLassoRanker/LarrazOliverasRodriguez-CarbonellRubio-2013FMCAD-Fig1-alloca_unknown-termination.c.i_Iteration6_Lasso+nonterminationTemplate.smt2`.
Paired directly, same binary, same file, 24 s each: lever `0` → `unknown`,
lever `1` → **`unsat`**, and the benchmark's own `(set-info :status unsat)`
agrees with the armed arm.

## Part D — the A/B

One binary (release `smtcomp_cli`, sha256 `bc8adc98…59e32`), two env values,
both arms back to back on the same file on the same pinned core with the arm
order alternating per file, 24 s / 8 GiB. s6, this lane's pairs `5,13` and
`6,14`; **all four logical cores ran at once** to fit the window, so each
physical core carried two sweeps. That inflates timeouts on BOTH arms of every
file — conservative for a ship gate, not for a gain, and every gain below was
re-checked 3× per arm.

| division | rows | A decided | B decided |
|---|---:|---:|---:|
| **QF_NIA** (pinned target) | **200** | **82** | **80** |
| **QF_NRA** (control) | **200** | 124 | 124 |
| **UFNIA** (target) | **200** | **54** | **61** |
| **QF_NIA held-out draw** | **200** | 85 | 85 |

**Disagreements (one arm `sat`, the other `unsat`): 0 of 800.** The control
moves nothing, which is what a control in the Real-sorted division has to do.

15 raw movers, each re-run three times per arm and classified only when all
three passes agree:

| division | STABLE-GAIN | STABLE-LOSS | UNSTABLE |
|---|---:|---:|---:|
| QF_NIA (pinned) | 1 | **2** | 1 |
| QF_NRA (control) | 0 | 0 | 0 |
| UFNIA | **7** | 0 | 0 |
| QF_NIA held-out | 2 | **1** | 1 |
| **total** | **10** | **3** | **2** |

The seven `UFNIA` gains are all `unknown → unsat` (`f2_rw160`, `f2_rw120`,
`f2_rw163`, `t3_rw96`, `t3_rw25`, `t3_rw21`,
`int_check_bvugt_bvneg_ltr_inv_g`). The pinned `QF_NIA` gain agrees with the
benchmark's own `(set-info :status unsat)`.

### D1 — what the three losses are

All three are `unsat → unknown`: files the shipped arm refutes and the armed
arm does not. Nothing unsound happened; `unknown` is a first-class result. What
was lost is TIME. Arming does two things to the refinement loop — it emits
lemmas (median 76 per reached file over up to 47 rounds) and it widens
`RefinementSetup::refine`, which also grants the loop a larger share of the
caller's remaining budget (§C). On a file some LATER route in the ladder
refutes, spending that budget in the relaxation starves the route that was
going to decide it. That is a scheduling cost, not a lemma defect.

## Decision

**1. The lever stays DISARMED and this ADR is `proposed`.** The criterion was
0 stable losses and 0 flips with at least one stable gain, on the pinned list
AND the held-out draw. Flips: **0 of 800**, met. Stable gains: **10**, met on
both `QF_NIA` populations and on `UFNIA`. Stable losses: **2 pinned, 1
held-out** — **not met**, so nothing ships ON.

**2. [ADR-2112]'s decision 4 is REFINED, not overturned.** It said not to build
a single nonlinear lemma class, on the evidence that z3's own order class is
load-bearing on 3 of the 75 files z3 decides. Measured on OUR portfolio the two
classes are worth **10 stable gains across 800 files with zero flips**, and
**7 of those are in one division** (`UFNIA`, 54 → 61, +13 %). The classes are
not worthless to us. What costs more than they pay, on `QF_NIA`, is the loop
that hosts them.

**3. The next lane's question is the SCHEDULE, not the lemma.** All three
losses are budget starvation of a later ladder route, and §C's widened `refine`
predicate is the mechanism. Separating "emit these lemmas" from "grant the loop
a larger slice" is a one-line experiment that the three named losing files can
score directly.

**4. The ceiling is the relaxation.** §C1 measured the pass reached on 59 of
116 undecided rows; the other 67 never produce a spurious model because the
linear DPLL(T) cannot solve the relaxation inside its slice. No lemma class can
decide a file whose relaxation never returns, and that bounds every number in
Part D.

## Gates, with counts

| gate | result |
|---|---|
| `cargo fmt --all --check` | clean |
| `cargo-serialized.sh clippy --workspace --all-targets --all-features -- -D warnings` | **clean** (the battery's exact lint) |
| `cargo check --workspace --all-targets` (default features) | clean |
| `run-dispatch-reason-suites.sh` | **28 of 28 green**, every one a nonzero count |
| `cargo test -p axeyum-solver --lib --features full -- --skip reconstruct::` | 1644 passed, 2 failed — both `auto::tests` wall-clock flakes in a file this lane does not touch; re-run alone **2 passed, 0 failed in 4.70 s** |
| `progress_frontier --features full -- --test-threads=1` | **12 passed, 0 failed**; on a quiet frame (load 5.5 → 6.5, scale 1.08x) `FRONTIER nia_unsat = 40 (baseline 40)`, no `REGRESSION` |
| `config_registry::tests` | **18 passed, 0 failed** |
| mutation `nia-order-lemmas` | baseline **27 green**; 2 mutations both MEASURED, killing **5** and **2**; `--check-anchors` `suites=162 anchors=1124 stale=0` |
| `check-config-registry-staleness.py` | 516 entries, **0 unexplained** |
| `check-merge-hygiene.sh` / `check-links.sh` | PASS / `all links ok` (+ both reference-style definitions hand-checked) |

**The six `z3` differential fuzzes were NOT RUN**, and that is the largest hole
in this ADR's evidence: `nia_differential_fuzz`,
`qf_nia_bounded_product_differential_fuzz`,
`qf_nia_divmod_const_differential_fuzz`,
`qf_nia_divmod_var_differential_fuzz`, `qf_nia_iand_differential_fuzz`,
`qf_nia_pow2_differential_fuzz`. The lever is OFF, so they would have exercised
the shipped route and not this one — but that is a reason they were low value
here, not a reason they were run. Any lane that arms this lever must run all
six with a NONZERO count in BOTH arms first.

## Consequences

**Easier.** The two absent classes exist, are valid by construction, and are
one env variable away. `reachability.sh` gives any lane the per-file "did the
refinement loop even run" classification in one command, which is the number
every future `nia_linearize` experiment needs before it starts.

**Harder.** Nothing while the lever is `0`: the shared-factor index is never
built and `timed_refine` cannot reach the pass.

**Revisited when.** The scheduling experiment in decision 3 lands, or the
relaxation's round-0 `unknown` rate on the 67 files improves. Either changes
Part D's denominators.

[ADR-2112]: adr-2112-qf-nia-what-the-clause-estimate-counts.md
[ADR-2106]: adr-2106-derived-ladder-order.md
