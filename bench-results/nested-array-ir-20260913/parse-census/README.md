# The parse gate, counted over the whole population (2026-09-13)

**29,564 files, every one of them, through the real parser.** Not a sample.

    division   files    parse ok            nested-array refusal
    AUFLIRA   20,011    1,367   ( 6.8%)     18,644   (93.2%)
    ABV        4,975      473   ( 9.5%)      4,502   (90.5%)
    ALIA       3,098       70   ( 2.3%)      3,028   (97.7%)
    AUFNIRA    1,480      504   (34.1%)        976   (65.9%)
    TOTAL     29,564    2,414   ( 8.2%)     27,150   (91.8%)

Two things this settles.

**1. The blocked count is 27,150, not 29,564.** The brief attributed the four
divisions' whole population to this refusal. 2,414 files parse today.

**2. `nested array element sort is unsupported` is the ONLY parse failure in
these four divisions.** Not the largest — the only one. The histogram has
exactly one non-`ok` bucket per division. (The message string embeds the
offending sort's `Debug`, so it is unique per file; `parse-census.py` normalises
to the constant prefix, without which the histogram has one bucket per file and
cannot count anything.)

## Two independent instruments, exact agreement

`census_nested.py` is a textual scan — s-expression walk, comment stripping,
0-arity `define-sort` alias expansion — that shares no code with the Rust
parser. Its per-division counts are `textual-census.tsv`:

    AUFLIRA  18,644     ABV  4,502     ALIA  3,028     AUFNIRA  976

**Identical to the parser's refusal counts in all four divisions.** Neither
instrument is the sole witness to its own number.

Cross-check on a fifth division the scanner was not tuned on: AUFDTLIRA,
**488 of 11,043 = 4.4%**.
[ADR-1927](../../../docs/research/09-decisions/adr-1927-a-ladder-rungs-fragment-refusal-is-a-decline-not-the-querys-verdict.md)
measured that division's parse-gate refusal at 5 of ~200 sampled files (2.5%)
through the full ladder. Expected 8.8 at p=0.044, observed 5 — 1.4σ, consistent.

## What this does NOT say

It does not say 27,150 files become decidable. **Parse is the first gate of
all**, so a parse refusal hides every gate behind it by construction
([ADR-1927](../../../docs/research/09-decisions/adr-1927-a-ladder-rungs-fragment-refusal-is-a-decline-not-the-querys-verdict.md)),
and a blocked count is an upper bound on a reachable count
([ADR-1945](../../../docs/research/09-decisions/adr-1945-a-blocked-count-is-not-a-reachable-count-and-two-sequential-caps-are-not-two-caps.md):
143→6, 51→2, 173→10, 84→49).

The 2,414 files that parse are the natural experiment that bounds it: same
divisions, same benchmark families, same solver, parse already behind them.
They are pinned in `../lists/<DIV>.parseok.txt` and measured next.

## Reproducing

    cargo build --release -p axeyum-smtlib --example parse_rate
    python3 bench-results/nested-array-ir-20260913/parse-census.py \
        target/release/examples/parse_rate <out-dir> AUFLIRA ABV ALIA AUFNIRA
    python3 bench-results/nested-array-ir-20260913/census_nested.py \
        /nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/{AUFLIRA,ABV,ALIA,AUFNIRA}

Binary built at `bfbd97dec`, verified newer than every `crates/**/*.rs`.
