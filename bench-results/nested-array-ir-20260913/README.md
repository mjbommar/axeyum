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

## What it found

The decision and the full derivation are
[ADR-1955](../../docs/research/09-decisions/adr-1955-the-nested-array-sort-is-the-first-of-three-gates-and-the-only-one-the-ir-owns.md).
In four numbers:

1. **27,150 blocked, not 29,564** (`parse-census/`) — the whole population
   through the real parser, with a second instrument agreeing exactly.
2. **A flat `(Array Int Real)` read-over-write is already `unknown`** while the
   same query with `Int` or `(_ BitVec 64)` is `unsat` (`probes/`). That rules
   AUFLIRA and AUFNIRA's **19,620** files out on a gate the IR does not own.
3. **Currying reaches 64.1% of ALIA, 50.6% of ABV, 0.0% of AUFLIRA**
   (`outer-use-census.py`) — the no-IR-change alternative, sized rather than
   assumed away.
4. **The family-matched control rate is 25.2% for ABV and 0 of 28 for ALIA**,
   which puts the whole three-gate chain at **~1,135 reachable files of 27,150**.
   All 126 decided files were re-run against z3 4.13.3 and cvc5 1.3.4
   (`parseok/ref-abv-alia.tsv`). No disagreement — but on ABV **neither
   reference decides one of the 119**, so that half of the check had no
   opportunity to fire and is reported as vacuous rather than as a pass.

## Files

| file | what it is |
|---|---|
| `mklist.py` | pins the four 200-file samples, FULL-SPAN (`round(i*(n-1)/199)`), copied from the board-six lane. Lists committed before any measurement. |
| `census_nested.py` | a parser-**independent** textual scan for `(Array A B)` with an array component, after 0-arity `define-sort` alias expansion. Positive and negative controls in `controls/`. This is the denominator the Rust refusal should agree with; two independent instruments answering the same question. |
| `parse-census.py` | the whole population through `parse_rate`, histogrammed. The reason string embeds the offending sort's `Debug`, so normalising to the constant prefix is load-bearing: without it the histogram has one bucket per file. |
| `outer-use-census.py` | how the OUTER array of a nested sort is actually used — `select` / `store` (curryable) versus equality, binder, or function argument (not). Deliberately partial in the safe direction: every construct it cannot follow counts as blocking, so it can only under-state curryability. Controls in `probes/`. |
| `shard-run.sh`, `build.sh`, `launch.sh` | the board protocol (24 s, 8 GiB, pinned core, arms interleaved per file with a rotating order), with `AX_BIN`/`ARMS` so two binaries can be A/B'd on one file back to back. |
| `summarize.py` | decide rate per division **and** the disagreement check. Exit 1 on any verdict contradicting a declared `:status` or another arm, exit 2 on an empty run — verified to fire on all three. |
| `probes/` | the gate-isolation queries. Each pair differs in exactly one token. Pinned as a test in `crates/axeyum-solver/tests/nested_array_gate_map.rs`. |
| `parseok/` | the control sweep's per-shard TSVs. |
