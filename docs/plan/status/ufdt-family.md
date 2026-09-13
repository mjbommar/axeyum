# Lane: ufdt-family — the three UFDT siblings censused whole, and the rung that ate UFDTNIRA's clock

<!-- plan-section: lane-status -->

**Lane ufdt-family (`DONE`, ufdt-family, 2026-09-13).** `UFDTNIRA`, `UFDTLIRA`
and `UFDT` were briefed as one target — the siblings of `AUFDTLIRA`, which went
0 → 110 in a day on datatype and dispatch work — with the question "how much of
that transfers?" **Most of it already had**, and the brief's own board row was
stale by 69 files: `UFDTNIRA` is **74 / 200 on the current tree, not 5**, and
its winnable set is 109, not 178.

All four divisions are then censused over their **whole** winnable sets (316
rows) at the pinned boards' own envelope. What is left is **two** targets, and
only one of them is a datatype capability.

ADR: [ADR-1975](../../research/09-decisions/adr-1975-valid-universal-elimination-spends-24-seconds-to-prevent-a-107-millisecond-refutation.md)
· artifact: [`bench-results/ufdt-family-20260913/`](../../../bench-results/ufdt-family-20260913/README.md)
· A/B: [`AB.md`](../../../bench-results/ufdt-family-20260913/AB.md)

## The board rows, re-measured

| division | pinned board | **here** | z3 | cvc5 | best ref | winnable (was) |
|---|---:|---:|---:|---:|---:|---:|
| UFDTNIRA | 5 | **74** | 173 | 183 | 183 | **109** (178) |
| UFDTLIRA | 66 | **105** | 181 | 158 | 181 | **76** (115) |
| UFDT | 22 | **31** | 66 | 78 | 80 | **51** (60) |
| AUFDTLIRA | 0 | **96** | 176 | 176 | 176 | **80** (176) |

**901 independent comparisons against `:status`, z3 4.13.3 and cvc5 1.3.4,
0 disagreements.** No zero is vacuous; `summarize.py` exits non-zero on one.

## What holds each, and the two splits the census had to make

- **`UFDTNIRA` is COST-bound.** 93 of 103 classified rows are CLOCK, and **56
  are one rung**: valid-universal elimination runs one quantifier-free sub-solve
  per top-level assertion, each handed the ladder's whole remaining clock. 69 of
  the pinned 200 spend the ENTIRE budget inside it and give up PAST the deadline
  (median 46 ms over, **no fast declines at all**). Across the four divisions
  that rung is the bounding route on **167 of 800 files and DECIDES 0**.
- **`UFDTLIRA`, `UFDT` and `AUFDTLIRA` are SHAPE-bound by ONE predicate.** The
  three datatype-**exactness** preconditions (ADR-1920/1935/1946) are **124 of
  316 rows** — the largest blocker family on this board — every one declining
  with a median 23.9 s of 24 s UNSPENT.

Neither was visible without a split: `quantified solve time budget exhausted
after <stage>` is **four rungs sharing one string**, and `mbqi declined an
unsupported fragment: …` is at least **four causes sharing a prefix**. That is
ADR-1956's defect one stage up, twice. Merged, `UFDTNIRA` reads "the quantified
ladder is slow" — a finding with no lever in it.

Also measured: **ADR-1956 holds on four more divisions** (0 of 316 rows reach
the instantiation round ceiling) and **no nested-array refusal appears at all**
(0 of 316), so ADR-1965's array-IR ceiling does not reach here.

## What landed — the reserve, shipped ON at a value the ceiling did not pick

| arm | UFDTNIRA | UFDTLIRA | UFDT | AUFDTLIRA | UF (control) |
|---|---:|---:|---:|---:|---:|
| ceiling `=1` | **74 → 93 (+19 / −0)** | 105 → 105 | 31 → 31 | 96 → 96 | 90 → 88 (**−2**) |
| **shipped `=4`** | **73 → 92 (+19 / −0)** | 105 → 105 | 31 → 31 | 96 → 96 | 90 → **90 (0 / 0)** |

**0 sat↔unsat flips in 4,000 solves.** The two arms gain the **identical set**
of 19 files, so the gain is not an artefact of an extreme setting; the control
is what separates them. All 19 re-run 3x per arm: **19 of 19 stable GAIN, 0
unstable**, 55 comparisons against `:status`/z3/cvc5, **0 disagreements and 0
rows nothing could check**. Noise floor: three independent base-arm runs over
800 files disagree on **one** named file — a band of 0–1 against +19.

**The generalisable half:** a one-way ceiling answers *"is anything
reachable?"*, never *"what should the constant be"*. ADR-1970 ran the ceiling
and shipped OFF because the ceiling was worth nothing. A lane whose ceiling IS
worth something must still run the shipped value against the control — here the
ceiling costs 2 control files and the shipped value costs 0.

| what | where |
|---|---|
| `QuantValidUniversalReservePolicy` + `AXEYUM_QUANT_VALID_UNIVERSAL_RESERVE`, default `LadderReserve { share: 4 }` | `crates/axeyum-solver/src/auto.rs` |
| `QUANT_VALID_UNIVERSAL_LADDER_RESERVE_SHARE` registry entry, dated to the artifact | `crates/axeyum-solver/src/config_registry.rs` |
| soundness-negative suite, all three arms, `Sat` fixtures pinned `Sat` | `crates/axeyum-solver/tests/quant_valid_universal_reserve_row.rs` |
| suite registration | `hooks/pre-push` |
| `quant-valid-universal-reserve`: 3 mutations, **3 killed, exactly 1 test each** | `scripts/tests/mutation_controls.py` |
| why the exactness predicate fails, with a control | `scripts/dt-exactness-field-shape.py` |
| census, both A/B arms, controls, re-checks, every derivation script | `bench-results/ufdt-family-20260913/` |

Gates, each with its own `test result:` line: solver `--lib --features full
-- --test-threads=4` **1739 passed**, `corpus_regression` 2, `dt_uf_gate` 10,
`dt_capability_1935` 20, `dt_constructor_arg_1942` 11, `dt_valued_result_1946`
12, `datatype_solve_path` 3, `quant_ladder_rung_refusal_declines` 3,
`dispatch_rung_refusal_declines` 2, `unknown_reason_coverage` 7,
`quant_egraph_reserve_row` 6, `quant_valid_universal_reserve_row` 6,
`config_registry` (in `--lib`) 18. `check-suite-gating.py` PASS,
`check-links.sh` all links ok, `check-merge-hygiene.sh` PASS, clippy
`-p axeyum-solver --all-targets --features full -D warnings` clean. No
linear-arithmetic code was touched, so the five z3 differential fuzzes **did not
run**.

## The next lane on these divisions: the exactness predicate, 124 rows

All three MBQI refusals rest on `datatype_expansion_is_exact`, which is false
exactly when a constructor field has sort `Datatype(_)` — a nested or recursive
datatype. `scripts/dt-exactness-field-shape.py` parses the benchmark TEXT rather
than going through the solver:

| population | n | nested (terminating) | recursive | flat |
|---|---:|---:|---:|---:|
| the 124 exactness-refused rows | 124 | **97** | 27 | **0** |
| the other 192 winnable rows *(control)* | 192 | 101 | 2 | 86 |

Not one refused file is flat and 86 of the control's 192 are, so the instrument
is measuring the right thing; and **78 % of the refused population is nested but
not recursive**, with field-chain depth ≤ 6 (51 at depth 2). A recursive
tag/field expansion **terminates** on those 97 with no depth bound and therefore
no new soundness story — the move ADR-1965 made one level out for the nested
ARRAY sort. Only 27 need a bounded unfolding.

But 101 control files are nested too and are not refused, so nesting is
necessary and not sufficient: **124 is the blocker count, not a reachable
count**, and this project's tally (143→6, 173→10, 934→0) says those differ a
lot. Two things to do first, in order: **run ADR-1966's check on the three
refusal sites** (a rung below may own the construct, which makes this a DECLINE
fix rather than a capability — this lane did not try it), and note that
`UFDTLIRA`'s winnable is **23 of 76 satisfiable** while `AUFDTLIRA`'s is 0 of
80, so a refutation-only fix ceilings differently per division.

<!-- plan-section: landed-changes -->

| 2026-09-13 | ufdt-family | The three `UFDT` siblings censused over their WHOLE winnable sets (316 rows, four divisions) — and the brief's board row was **stale by 69 files**: `UFDTNIRA` is **74 / 200 on the current tree, not 5**. What is left is TWO targets. `UFDTNIRA` is COST-bound: **56 of 109 winnable rows are one rung**, valid-universal elimination, which holds the ENTIRE 24 s budget and gives up PAST the deadline (median 46 ms over, no fast declines), and which across the four divisions is the bounding route on **167 of 800 files and DECIDES 0**. `UFDTLIRA`/`UFDT`/`AUFDTLIRA` are SHAPE-bound by ONE predicate: the three datatype-EXACTNESS preconditions are **124 of 316 rows**, sized and handed off with a static instrument showing **97 of 124 are NESTED but not recursive** (depth ≤ 6) against a control where 86 of 192 are flat. Both findings needed a split the census would not have made — `budget exhausted after <stage>` is FOUR rungs sharing one string and `mbqi declined an unsupported fragment: …` is at least FOUR causes sharing a prefix (ADR-1956's defect, one stage up, twice). The reserve the first implies is built as a one-binary env lever, sized by its one-way CEILING arm and then **shipped at a DIFFERENT value**: ceiling `=1` is +19/−0 on `UFDTNIRA` but loses **2** `UF` control files reproducibly; `=4` gains the **IDENTICAL 19** and loses **0**. Ships **ON at `share = 4`**: 0 sat↔unsat flips in 4,000 solves, 19 of 19 re-checked 3x per arm as stable GAIN, 55 comparisons vs `:status`/z3/cvc5 with 0 disagreements and 0 unopposed rows, noise band 0–1 files over three base-arm runs, 901 comparisons on the census board with 0 disagreements, 3 mutations 3 killed exactly one test each; ADR-1975 |
