# Gate-isolation probes

Each probe is the smallest query that reaches exactly one gate, and the probes
come in **pairs that differ in one token**. That is the whole method: a single
`unknown` says nothing, because a query can be undecided for any of a dozen
reasons; an `unsat`/`unknown` pair over queries that differ only in the element
sort names the gate.

Measured 2026-09-13 through `smtcomp_cli --timeout-ms 24000` at `bfbd97dec`.
The `p*` verdicts are pinned as a test — `crates/axeyum-solver/tests/nested_array_gate_map.rs`,
named in `hooks/pre-push` — so this table is checked, not remembered.

| probe | shape | verdict | what it shows |
|---|---|---|---|
| `p1-flat-real` | `(Array Int Real)`, store-then-read at the SAME index | `unsat` | constant folding decides it; not evidence the array theory engaged. This probe exists to show why `p5` is the right question. |
| `p2-flat-int` | `(Array Int Int)`, same | `unsat` | |
| `p4`/`p8-row-bv` | `(Array (_ BitVec 8) …)` ROW at symbolic indices | `unsat` | |
| `p10-row-bv64` | `(Array (_ BitVec 64) (_ BitVec 64))` ROW | **`unsat`** | ABV's real width works flat |
| `p6-row-int` | `(Array Int Int)` ROW | **`unsat`** | ALIA's leaf works flat |
| `p5-row-real` | `(Array Int Real)` ROW | **`unknown`** | **the second gate.** No nesting in this query. `give-up kind=Incomplete`, `attempts=16` — the ladder ran to the end (ADR-1936), so the row is classified. `scalar_alia_auflia_arrays_supported` (`auto.rs:6098`) requires `!features.has_real`. |
| `p3-nested-int`, `p7-row-nested`, `p9-row-bv-nested` | nested | `unknown` | refused at parse — the first gate |
| `q1-uf-array-int` | `(declare-fun row (Int) (Array Int Int))`, congruence + read | **`unsat`** | the curry target exists |
| `q2-uf-array-bv` | same at 64-bit | **`unsat`** | |
| `q3-uf-array-store` | `store` into a UF-returned array | **`unsat`** | currying can express outer writes, not only outer reads |

`p5` versus `p6` is the pair the whole ADR turns on: the same query, `Int`
swapped for `Real`, opposite verdicts, and **neither has a nested array in it**.

## Controls for `outer-use-census.py`

`c-*.smt2` are the census's own controls, one per classification it makes:

| file | expected | why |
|---|---|---|
| `c-eq` | BLOCKED `eq` | outer array equality — needs extensionality, not expressible by currying |
| `c-binder` | BLOCKED `binder` | a quantified variable of outer-array sort becomes a second-order quantifier |
| `c-arg` | BLOCKED `arg` | an outer array passed to a function |
| `c-noouter` | no outer occurrence at all | a flat array must not be counted |
| `p3`, `p7`, `p9` | CURRYABLE | every occurrence is `select` or `store` |

All six behave as stated. A census with no negative control cannot tell "0%
curryable" from "the scanner never fired".
