# Lane: ufnia-uflia — Tier-1 #2 and #3 censused, and the blocker they name sized at 2

<!-- plan-section: lane-status -->

**Lane ufnia-uflia (`DONE`, ufnia-uflia, 2026-09-13).** `UFNIA` and `UFLIA` are
censused over their **whole** winnable sets (129 rows, not a sample) on the
current tree. The largest family in both — 23 rows each — is attributed to ONE
route: **`q:egraph` holds a median 94 % / 88 % of the 24 s budget on 44 of those
46 rows, declines, and leaves full MBQI and the finite-model finder nothing.**
The same run measures what that budget buys: the rung is entered on ~61 % of
files and decides **1 of 200** (`UFNIA`) and **8 of 200** (`UFLIA`).

The ladder reserve that implies was built as a one-binary env lever and **sized
by its own CEILING arm**: `46 blocked rows → +4 / −2 over 400 files` after
re-checking, `UFLIA` net zero, and a quantified `AUFLIA` control flat at 0/0.
**The lever ships OFF.** A measured *do not build this*.

ADR: [ADR-1970](../../research/09-decisions/adr-1970-the-egraph-rung-eats-the-quantified-clock-to-decide-one-file-in-two-hundred.md)
· artifact: [`bench-results/ufnia-uflia-census-20260913/`](../../../bench-results/ufnia-uflia-census-20260913/README.md)

## The board rows

| division | files | axeyum (here) | axeyum (pinned) | z3 | cvc5 | best ref | winnable |
|---|---:|---:|---:|---:|---:|---:|---:|
| UFNIA | 13,464 | **53** | 53 | 96 | 94 | 114 | 61 |
| UFLIA | 10,128 | **76** | 71 | 139 | 142 | 144 | 68 |

`UFNIA` reproduces ADR-1957's Tier-1 board exactly — the cross-check that this
lane's harness measures the same thing. `UFLIA` is +5 on board-six's row, from
other lanes' work landed since.

## The census, and the two labels it corrects

    by kind:  CLOCK 81   SHAPE 14   PARSE 2   OTHER 2   ROUND 1
              UNCLASSIFIED (ADR-1941) 29      no route trail 0

- **ADR-1957's "`UFNIA` is genuinely clock-bound" is half right.** Its 23-row
  first family gives up a median **61 ms past** the deadline; its 18-row second
  family (`e-matching: instantiation time budget exhausted`) gives up with a
  median **8,768 ms of 24,000 unspent**. ADR-1950's falsification mechanism
  firing on a family name again. No larger wall budget reaches those 32 rows.
- **ADR-1956 holds on two more divisions: 0 of 129 rows reach the instantiation
  round ceiling.** `AXEYUM_QINST_ROUNDS` buys nothing here.
- **No nested-array refusal in either division** — 0 of 129 — so ADR-1965's
  20,399-file ceiling does not reach these rows.
- ADR-1941 is doing real work: the `attempts=`-only rule would discard 121 of
  129 rows and leave `UFNIA`'s census with one.

## What landed

| what | where |
|---|---|
| `QuantEgraphReservePolicy` + `AXEYUM_QUANT_EGRAPH_RESERVE`, default `WholeBudget` | `crates/axeyum-solver/src/auto.rs` |
| `QUANT_EGRAPH_LADDER_RESERVE_SHARE` registry entry, dated to the artifact | `crates/axeyum-solver/src/config_registry.rs` |
| soundness-negative suite, all three arms, `Sat` fixtures pinned `Sat` | `crates/axeyum-solver/tests/quant_egraph_reserve_row.rs` |
| suite registration | `hooks/pre-push` |
| `quant-egraph-reserve`: 3 mutations, **3 killed, exactly 1 test each** | `scripts/tests/mutation_controls.py` |
| census, A/B, control, re-checks and every derivation script | `bench-results/ufnia-uflia-census-20260913/` |

Gates, each with its own `test result:` line: solver `--lib --features full`
**1736 passed**, `corpus_regression` 2, `quantifiers` 6, `quant_bool_model_sat`
15, `quant_ladder_rung_refusal_declines` 3, `dispatch_rung_refusal_declines` 2,
`unknown_reason_coverage` 7, `quant_egraph_reserve_row` 6, `config_registry` 18.
`check-suite-gating.py` PASS, `check-links.sh` all links ok. No linear-arithmetic
code was touched, so the five z3 differential fuzzes **did not run**.

## The next lane on these divisions should not build a scheduling fix

The 46-row family is attributed and its ceiling is measured. What is left is the
32-row family that stops with a third of the clock unspent — whose remedy is a
rung that does not exist, not a budget — and the 29 UNCLASSIFIED rows. The one
thing the ceiling arm does **not** rule out is instance *selection*, which
`uf-quantified-loss-attribution-2026-09-09` named for `UF`; `q:egraph`'s 61 %
entry rate against its 0.5–4 % decision rate is now the denominator to measure
that against.

<!-- plan-section: landed-changes -->

| 2026-09-13 | ufnia-uflia | Tier-1 #2 and #3 censused over their WHOLE winnable sets (129 rows): the largest family in both — 23 rows each — is `q:egraph` holding a median **94 % / 88 %** of the 24 s budget, declining, and starving full MBQI and the finite-model finder, while that rung ENTERS 61 % of files and DECIDES **1 of 200** (`UFNIA`) and **8 of 200** (`UFLIA`). The ladder reserve that implies is built as a one-binary env lever (`AXEYUM_QUANT_EGRAPH_RESERVE`, default OFF) and **sized by its own one-way CEILING arm**: `46 blocked rows → +4 / −2 over 400 files` after re-running every moved row 3x per arm, `UFLIA` net zero, quantified `AUFLIA` control (route hit rate 57 %) flat at 0/0, **0 sat↔unsat flips in 1,200 solves**. A measured DO NOT BUILD. Two labels corrected: ADR-1957's "`UFNIA` is genuinely clock-bound" is half right (18-row second family gives up with a median **8,768 ms of 24,000 unspent**), and **0 of 129** rows reach the instantiation round ceiling, so ADR-1956 holds on two more divisions; ADR-1970 |
