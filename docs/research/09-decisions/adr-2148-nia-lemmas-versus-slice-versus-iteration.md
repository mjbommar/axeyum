# ADR-2148: the QF_NIA lemma lever, split three ways — the losses are the lemmas, the gains are the iteration

Status: accepted
Index-summary: ADR-2136 measured its order/monotonicity lemma lever at 10 stable gains and 3 stable losses and blamed the losses on the SLICE it also widened. **Traced at head, that is not what happened**: all three losing files carry small-domain splits, so the shipped arm already had the wide slice and is decided by the refinement loop ITSELF in 2–6 s; the armed loop adds 20–39 lemmas at round 0 and does not refute the same system in the same slice. The lever was split three ways — `AXEYUM_NIA_REFINE_SHARE` for the slice (ships `3`), and `AXEYUM_NIA_ORDER_LEMMAS` as a MODE: `1` both classes, `2`/`3` one class, `4` **iterate with tangent planes only**, the control ADR-2136 never ran. On its own 13 moved files: the share is the mechanism of no loss and two gains; the CLASSES are the mechanism of every loss in every combination that emits them and are worth exactly `305` and `39`; and **eight of the ten "lemma" gains are ITERATION gains** — mode 4 decides them with no class lemma at all and loses nothing, because on an envelope file it is the shipped code. **Two four-population A/Bs** of mode 4 against the shipped default (800 files each, interleaved, movers re-checked 3× per arm): 0 disagreements, 0 `:status` contradictions, **0 stable losses**, 6 and 8 stable gains, control `QF_NRA` 0/0. **The `UFNIA` held-out draw** (seeded, disjoint, 200 files): 51 → 58, **6 stable gains, 0 losses**. **SHIPS**: `NIA_ORDER_LEMMAS_ARMED = 4`, `NIA_REFINE_SHARE = 3`; `UFNIA` 54 → 61 pinned (+13 %). The `QF_NIA` held-out draw has 0 movers, stated rather than absorbed. The classes stay OFF behind the lever: a 2-for-2 trade against the `splits > 0` Farkas family. Gates: 17 z3 fuzz tests green in BOTH arms, `nia_unsat` 40/40, 33 dispatch/reason suites green, lib sweep 1667/0.
Index-status: accepted
Date: 2026-09-17

## Context

[ADR-2136] built z3's order and monotonicity lemma classes into
`nia_linearize.rs` behind `AXEYUM_NIA_ORDER_LEMMAS` (shipped `0`) and measured
them on 800 files: **10 stable gains, 3 stable losses, 0 flips**. Its D1
attributed all three losses — `unsat → unknown` on
`From_T2__ex36…`, `From_T2__n-7…` (pinned) and `From_T2__n-21…` (held-out) —
to a scheduling cost: arming also widened `RefinementSetup::refine`, which
both let the refinement loop iterate and granted it `remaining / 3` of the
budget instead of the 600 ms hang guard, so a later ladder route was starved.
The stock-take's queue item 3 asked this lane to separate "emit the lemmas"
from "widen the slice" and let the three losing files score it.

This ADR does that, and then keeps cutting, because the first cut refuted its
own premise. Every number is in
[`bench-results/nia-refine-share-20260917/`](../../../bench-results/nia-refine-share-20260917/README.md).

## Part A — the sizing: what the three losses actually are

Twelve of the 13 scoring files reproduce at head (`f7cd4195f`) 3× per arm
(`39.smt2` is a marginal gain, B 2/3 then 1/3). Traced per route in both arms
(`--trace` + `AXEYUM_NIA_DEBUG=1`), the three losses share one shape:

| file | `mccormick`/`splits` | shipped arm | armed arm |
|---|---:|---|---|
| `ex36` | 0 / 136 | **`nia-linearize` decides `unsat` in 3.2 s** of its 6.65 s slice (round 3) | `nia-linearize` runs the same 6.65 s out (round 3, 0.77 s left), `int-blast-ladder` 13.3 s, `unknown` |
| `n-7` | 0 / 82 | **`nia-linearize` decides `unsat` in 2.2 s** (round 1) | adds 20 lemmas at round 0; the lazy LIA driver spends the whole 6 s on round 1 ("exhausted the configured timeout after 94 rounds") |
| `n-21` | 0 / 100 | `nia-linearize` at the slice's edge: at a 60 s budget both arms decide `unsat` by `nia-linearize`, **5.9 s shipped vs 6.3 s armed** (3 interleaved pairs); at 24 s the slice is 6.65 s | the same, and does not fit |

**All three carry small-domain splits, so `refine` is already true and the
slice already `remaining / 3` in the SHIPPED arm.** Arming widens nothing on
these files, and no later route is starved: the shipped arm is decided by the
refinement loop ITSELF, and the armed loop — 20–39 extra order/monotone lemmas
at round 0, reshaping the relaxation from the first cut — does not refute the
same system in the same slice. D1's mechanism is not what happened.

## Part B — the split (`1505f035c`)

`refinement_setup` now computes two things that one boolean used to carry:

- `refine: has_envelopes || (order_lemmas.armed() && has_products)` decides
  ITERATION only — whether a spurious model is cut off or ends the loop.
- `grant: slice_grant(has_envelopes, has_products, refine_share)` decides the
  SLICE: `Envelopes` (`remaining / NIA_MCCORMICK_BUDGET_SHARE`, the committed
  share) when the entailed-bound passes produced anything, `ProductShare(n)`
  (`remaining / n`) when they produced nothing and the new lever
  `AXEYUM_NIA_REFINE_SHARE=n` is nonzero, and the 600 ms `HangGuard`
  otherwise. It does not take the lemma lever at all.

`AXEYUM_NIA_ORDER_LEMMAS=1 AXEYUM_NIA_REFINE_SHARE=3` is byte for byte
ADR-2136's B arm (`the_share_lever_draws_its_own_slice` pins share 3 equal to
the `Envelopes` slice). Both levers are registered; five unit tests pin the
2×2 (`the_slice_grant_does_not_read_the_lemma_lever`,
`the_iteration_gate_does_not_read_the_share_lever`, the slice arithmetic, the
lemma count under three shares, the shipped constant); mutation suite
`nia-refine-share` restores each of three couplings and each kills exactly one
distinct test.

## Part C — the 2×2 on the 13 files (share × lemmas)

One binary, four env settings, 3 passes per arm interleaved within each pass,
24 s / 8 GiB, s7 cores 1 and 3; DECIDED only when 3 of 3 decide.

| | L0S0 shipped | L1S0 lemmas, hang guard | L0S3 no lemmas, share 3 | L1S3 = ADR-2136 B |
|---|---:|---:|---:|---:|
| of the 10 gains kept | 0 | **8** | 0 | 10 |
| of the 3 losses kept | 3 | **0** | 3 | 0 |

The share is not the mechanism of any loss (`L1S0` loses all three) and is
the mechanism of two gains — `t3_rw25` and `Larraz…` have no entailed-bound
structure and are decided only with `ProductShare(3)`; the other eight gains
decide inside the hang guard (106–606 ms) or already had the wide slice
(`305`, `39` carry splits). `L0S3` gains nothing: a wider slice with only
tangents to cut and no iteration is the budget tax `refine` was written to
refuse. **No quadrant ships.**

## Part D — cut again: which CLASS, and is it the classes at all?

The lever became a mode (`770d23545`): `1` both classes (ADR-2136), `2` the
order class alone, `3` the monotonicity class alone, `4` **neither** — the
loop iterates on a product-bearing query exactly as the armed arms do and cuts
spurious models with tangent planes only. Mode 4 is the control ADR-2136 §C
introduced in the same lever and never measured apart. Same protocol, cores 1
and 3 (classes) and 5 and 7 (mode 4).

| file | shipped | Both S3 | Order S0 / S3 | Monotone S0 / S3 | **Tangents S0 / S3** |
|---|---|---|---|---|---|
| `n-21` (loss) | edge¹ | ✗ | ✓ 10.7 s / ✓ | ✓ 9.3 s / ✓ | edge¹ / edge¹ |
| `305` (gain) | ✗ | ✓ | ✓ / ✓ | ✓ / ✓ | ✗ / ✗ |
| `39` (gain) | ✗ | ✓ | ✓ / ✓ | ✗ / ✗ | ✗ / ✗ |
| `f2_rw160`, `t3_rw96`, `f2_rw120` (gains) | ✗ | ✓ | ✓ / ✓ | ✓ / ✓ | **✓ / ✓** |
| `t3_rw25` (gain) | ✗ | ✓ | 2/3 / ✓ | ✗ / ✓ | **✓ / ✓** |
| `t3_rw21`, `f2_rw163`, `int_check…` (gains) | ✗ | ✓ | ✓ / ✓ | ✓ / ✓ | **✓ / ✓** |
| `ex36` (loss) | ✓ | ✗ | ✗ / ✗ | ✗ / ✗ | **✓ / ✓** |
| `n-7` (loss) | ✓ | ✗ | ✗ / ✗ | ✗ / ✗ | **✓ / ✓** |
| `Larraz…` (gain) | ✗ | ✓ | ✗ / ✓ | ✗ / ✓ | ✗ / **✓** |

¹ decided by the shipped route at the slice's edge on a quiet box only; three
sweeps shared the host here. Envelope files run identical code under mode 4
and the shipped arm.

Three findings, each of which changes what [ADR-2136] should have said:

1. **Eight of the ten "lemma" gains are ITERATION gains.** The seven UFNIA
   files and `t3_rw25` are decided with no class lemma at all — mode 4, tangent
   planes only, inside the 600 ms hang guard (the per-round logs under the
   ADR-2136 arm show them building ONE order/monotone lemma per round, which
   was never the cut that mattered). `Larraz…` is decided by mode 4 with
   share 3. The classes are worth exactly `305` and `39`, both of which need
   the ORDER class (`39` fails under monotonicity alone).
2. **The losses are the classes, in every combination that emits them**, and
   they are `unsat → unknown` on the `splits > 0` Farkas/template family that
   the tangent loop refutes alone in 1–4 rounds. Either class alone keeps
   `n-21` (fewer lemmas than both, 39 → ≤ 20) and still loses `ex36` and
   `n-7`. Mode 4 loses none: on an envelope file it is the shipped code.
3. **The mechanism is neither the slice nor a later route.** It is the lazy LIA
   driver's search on the guarded implications the classes add — 20–39 of them
   at round 0 — on a relaxation it would otherwise refute in seconds. A
   per-round cap cannot separate the two populations (`305`/`39` need 26–28 at
   round 0; the losses build 20–39); an "only where the tangents stall" mode
   (`NiaRefinementNoNewLemma`) was written, unit-tested, and found INERT on the
   corpus — that decline occurs on **0 of 200 + 200** T1 ledger rows in
   `QF_NIA` and `UFNIA` (the tangent loop never stalls; it runs its slice out),
   so it was removed rather than shipped as a fourth arm nothing reaches.

## Part E — the A/B of the arm that keeps most: mode 4

Two four-population A/Bs of mode 4 against the shipped default, one binary
(`72816651…eaab`), interleaved per file with the arm order alternating, 24 s /
8 GiB, s7 — mode 4 with the hang guard on cores 1, 9, 3, 11 and mode 4 with
share 3 on cores 5, 13, 7, 15, all eight logical cores of four physical ones
at once (conservative for a ship gate, not for a gain; every mover re-checked
3× per arm on a quiet core). Pinned `QF_NIA`, `QF_NRA` (control), `UFNIA`, the
held-out `QF_NIA` draw ADR-2136 used (overlap with pinned 0/200).

| division | rows | shipped | mode 4, hang guard | shipped | **mode 4, share 3** |
|---|---:|---:|---:|---:|---:|
| `QF_NIA` (pinned) | 200/200 | 83 | 85 | 82 | 84 |
| `QF_NRA` (control) | 200/200 | 123 | 123 | 122 | 122 |
| `UFNIA` (pinned) | 200/200 | 54 | 60 | 54 | **61** |
| `QF_NIA` held-out | 200/200 | 81 | 81 | 82 | 81 |

**Disagreements 0 of 800 in each A/B; verdicts contradicting the benchmark's
`(set-info :status)` 0 of 800 in each; the control moves nothing.** Movers
re-checked 3× per arm:

| arm | raw | STABLE-GAIN | STABLE-LOSS | UNSTABLE |
|---|---:|---:|---:|---:|
| mode 4, hang guard | 8 | **6** (`UFNIA`) | **0** | 2 (both `sat` 6/6 on the quiet core) |
| **mode 4, share 3** | 10 | **8** (`Larraz…` + 7 `UFNIA`) | **0** | 2 (`DivMinus…` `sat` 6/6; `529.smt2`, the one raw held-out loss, `sat` 6/6 in both arms) |

The eight stable gains of the share-3 arm are exactly the eight files Part D
predicted. The `QF_NIA` held-out draw has no stable mover in either arm, and
the pinned `QF_NIA` gain is one file — mode 4's measurable effect is in
`UFNIA` (+7, 54 → 61, +13 %), which had no held-out draw. So the share-3 arm
was run against the shipped default on the seeded, disjoint 200-file `UFNIA`
held-out list ADR-2106's lane drew
(`bench-results/derived-order-20260915/heldout-lists/UFNIA.txt`, seed 20260915,
excluding every pinned path and every ledger row; overlap with the pinned list
0/200), four shards on cores 1, 3, 5, 7, same envelope:

| | rows | shipped | mode 4, share 3 | disagreements | `:status` contradictions | raw | STABLE-GAIN | STABLE-LOSS |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `UFNIA` held-out | 200/200 | 51 | **58** | 0 | 0 | 7 gains, 0 losses | **6** | **0** |

The one UNSTABLE raw gain (`test14-Microsoft.Boogie…get_IsAddrOf`) is `unsat`
6/6 in both arms on the quiet core. The six stable held-out gains
(`f2_rw166`, `f2_rw292`, `f2_rw268`, `f2_rw290`, `f2_rw62`, `t3_rw62`) are all
`unknown → unsat` in the same `2019-Preiner` family as the pinned seven.

## Decision

**1. Mode 4 with share 3 ships: `NIA_ORDER_LEMMAS_ARMED = 4`,
`NIA_REFINE_SHARE = 3`.** The refinement loop now iterates past a spurious
model on every product-bearing query, cutting with tangent planes, with a
third of the remaining budget — the same share the envelope case has always
had. Against the criterion: 0 stable losses on 1,800 file-runs, 0 flips, 0
`:status` disagreements, stable gains on pinned (8: `Larraz…` and seven
`UFNIA`) and on held-out (6, on the `UFNIA` draw). **On the `QF_NIA` held-out
draw the arm has 0 stable movers**, and this ADR ships on the division the
lever measurably moves — `UFNIA`, 54 → 61 pinned and 51 → 58 held-out — rather
than on `QF_NIA`, where its effect is one pinned file. That is a judgment about
which held-out list the criterion's gain clause is meant to guard, and it is
stated here so a reader can disagree with it.

**2. ADR-2136's two lemma classes stay OFF** (`=1`, `=2`, `=3` remain
selectable). Measured apart from the iteration they rode in on, they are worth
`305` and `39` (both `QF_NIA` held-out, both needing the order class) and cost
`ex36` and `n-7` (both `QF_NIA` pinned) in every combination that emits them.
A 2-for-2 trade with stable losses does not ship.

**3. [ADR-2136]'s D1 is corrected.** The three losses were never a starved
later route: the losing files already had the wide slice, and the shipped
arm's decision on them is the refinement loop's own. What arming cost was the
lazy LIA driver's search on 20–39 guarded implications added to a relaxation
it would otherwise refute in seconds. And eight of its ten gains were the
loop iterating at all, which its §C introduced as plumbing and never
measured. ADR-2136's decision 2 ("the classes are worth 10 stable gains") is
therefore revised to: the classes are worth 2, the iteration is worth 8 plus
6 more on a held-out draw.

**4. [ADR-2112]'s decision 4 stands, on different evidence.** "Do not build a
single nonlinear lemma class" was argued from z3's redundancy; measured on
our portfolio the two classes cost as much as they pay. What paid was
scheduling — letting the cheapest cut (the tangent plane) run more than once.

## Gates, with counts

| gate | result |
|---|---|
| `cargo fmt --all --check` | clean |
| `cargo-serialized.sh clippy --workspace --all-targets --all-features -- -D warnings` | clean |
| `cargo check --workspace --all-targets` | clean |
| six NIA z3 fuzzes + `nra_differential_fuzz`, `--features z3`, **shipped arm** (levers unset) | `nia_differential_fuzz` 2, `nra_differential_fuzz` 8, `qf_nia_bounded_product` 1, `qf_nia_divmod_const` 2, `qf_nia_divmod_var` 2, `qf_nia_iand` 1, `qf_nia_pow2` 1 — **17 passed, 0 failed** |
| the same seven, **new default arm** (`AXEYUM_NIA_ORDER_LEMMAS=4 AXEYUM_NIA_REFINE_SHARE=3`) | **17 passed, 0 failed** (same counts) |
| `cargo test -p axeyum-solver --features full --test corpus_regression` | **2 passed, 0 failed** |
| `cargo test -p axeyum-solver --lib --features full nia` | **52 passed, 0 failed** |
| `cargo test -p axeyum-solver --lib --features full -- --skip reconstruct::` (new default) | **1667 passed, 0 failed** |
| `run-dispatch-reason-suites.sh` (the pre-push hook's block, new default) | **33 of 33 suites green**, every count nonzero |
| `progress_frontier --features full -- --test-threads=1`, `taskset -c 0-7`, new default | **12 passed, 0 failed**; `FRONTIER nia_unsat = 40 (baseline 40)`, `nra_degree` 40/40, `bv_reduction` +9 / `lia_cuts` +9 / `string_bound` +32 PROGRESS (pre-existing); frames `scale 1.05–1.10x`, no NOT COMPARABLE, no REGRESSION; `bench-results/frontier/*.json` restored, not committed |
| `config_registry::tests` | **18 passed, 0 failed** |
| mutation `nia-refine-share` (new default) | baseline **33 green**; 3 mutations MEASURED, killing 1 / 2 / 2, three DIFFERENT kill sets each with its own named test; `--check-anchors` `suites=205 anchors=1190 stale=0` |
| `check-config-registry-staleness.py` | no unexplained staleness (4 rows TRIAGED for the caps resting on `order_and_monotone_lemmas`, whose body gained the mode gate) |
| `check-suite-gating.py` / `check-merge-hygiene.sh` / `check-lcg-raw-state.py` / `check-links.sh` | PASS / PASS / PASS / see the lane report |

## Consequences

**Easier.** The refinement loop's three knobs — iterate, which class, how much
budget — are three levers with a 2×2×4 any lane can A/B in one binary, and
`summarize-ab.py` refuses a short sweep, a flip, or a `:status` contradiction
instead of printing a percentage over it. The `UFNIA` held-out draw now has a
measured baseline (51 shipped, 58 new default) for the next lane.

**Harder.** A product-bearing `QF_NIA` query without entailed-bound structure
now spends up to a third of its remaining budget in the refinement loop where
it spent 600 ms; the A/B measured that at 0 stable losses on 400 `QF_NIA`
files, but a later route that was deciding such a file inside the last third
of the budget would show up as a loss on a population this did not sweep.

**Revisited when.** A lane finds the shape on which the order class does not
reshape a refutable relaxation (a cap keyed on the round's tangent count, or a
class emitted only for pairs with no exact split, are the untested
candidates), or the `QF_NIA` relaxation's round-0 `unknown` rate on the 67
files of ADR-2136 §C1 improves — that is still the ceiling on this division.

## Gates, with counts

PLACEHOLDER

## Consequences

PLACEHOLDER

[ADR-2136]: adr-2136-order-and-monotonicity-lemmas-for-nia.md
[ADR-2112]: adr-2112-qf-nia-what-the-clause-estimate-counts.md
