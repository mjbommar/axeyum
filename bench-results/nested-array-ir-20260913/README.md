# Nested array sorts: sizing before building (2026-09-13)

Lane `NESTED-ARRAY-IR`. The question: `crates/axeyum-ir/src/sort.rs` refuses a
nested array sort at parse

    parse error: unsupported: nested array element sort is unsupported

and four divisions — AUFLIRA (20,011), ABV (4,975), ALIA (3,098), AUFNIRA
(1,480), **29,564 files** — have no measurement of any kind. The lane brief
attributed all 29,564 to that refusal. This directory is the measurement that
says what the refusal actually costs, taken **before** any feature was built.

## Why this is measured and not assumed

The only prior data on these four divisions is
`bench-results/session-20260911-smtlib/coverage/blockmap.txt`, which sampled
**2–3 files per division** and carries its own `PARTLY REFUTED` banner: of its
20 rows, 13 have been re-measured at n≥40 and **ten were wrong**.

Two in-tree rules apply directly:

- [ADR-1945](../../docs/research/09-decisions/adr-1945-a-blocked-count-is-not-a-reachable-count-and-two-sequential-caps-are-not-two-caps.md)
  — a census attributing N files to a blocker is an **upper bound** on what
  removing it buys. Measured instances: 143→6, 51→2, 173→10, 84→49.
- [ADR-1927](../../docs/research/09-decisions/adr-1927-a-ladder-rungs-fragment-refusal-is-a-decline-not-the-querys-verdict.md)
  — a census taken through a ladder that stops at its first refusal measures
  the ORDER OF THE LADDER. **Parse is the first gate of all**, so a parse
  refusal hides every gate behind it by construction.

## Files

| file | what it is |
|---|---|
| `mklist.py` | pins the four 200-file samples, FULL-SPAN (`round(i*(n-1)/199)`), copied from the board-six lane. Lists committed before any measurement. |
| `census_nested.py` | a parser-**independent** textual scan for `(Array A B)` with an array component, after 0-arity `define-sort` alias expansion. Positive and negative controls in `controls/`. This is the denominator the Rust refusal should agree with; two independent instruments answering the same question. |

Results and their derivation are recorded in this README as they land.
