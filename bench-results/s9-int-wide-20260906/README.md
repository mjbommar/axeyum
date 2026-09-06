# S9 — ADR-1702 slice 2: wide integer literals reach the solver

Artifacts for the `s9-int-wide-parser` lane. Every number in
[`docs/research/11-design-review/2026-09-06-s9-int-wide-measured.md`](../../docs/research/11-design-review/2026-09-06-s9-int-wide-measured.md)
comes from a file here.

## Census

| file | what it is |
|---|---|
| `census-wide-int-literals.py` | scans a division listing for **bare numerals** above `i128::MAX` — the exact atom shape `parse.rs` feeds to `a.parse::<i128>()` — and reports the largest one's bit length, digit count, occurrence count, and syntactic position |
| `qf_uflia_wide_literal_census.tsv` | the census output over `bench-results/parity-lists/QF_UFLIA.txt` (200 files) |
| `qf_uflia_wide_literal_files.txt` | just the file column: the 26 files |
| `census_parser_crosscheck.txt` | the census's verdict against the real front door over all 200 files, both directions |

The census is a scan, not the parser, so it is cross-checked against the parser
over the **whole 200-file population**, not just its own hits: the front door
(`explain_corpus --list … 2000 --json`) classifies exactly 26 files as
`kind: wide-integer-literal`, and the two sets agree with zero difference in
either direction. Checking only the census's own 26 would have confirmed no
false positives and said nothing about false negatives.

## ADR-0376's ablation, re-run

`ADR-0376` (2026-08-04) deferred this widening on a measurement: with every
out-of-range literal removed from the problem, the six files cvc5 decides were
*still* `unknown`, so the binding constraint was the decision procedure and not
the literal type. A blocker recorded a month ago is a claim about a tree that no
longer exists, so it was re-measured before any code was written.

| file | what it is |
|---|---|
| `ablate-wide-literals.py` | rewrites a file two ways: `rescale` (every out-of-range numeral → a distinct `2^60 + i`) and `delete` (every top-level `assert` mentioning one is dropped) |
| `adr0376_target_six.txt` | the six files ADR-0376 measured cvc5 deciding |
| `ablation_rescale.tsv`, `ablation_delete.tsv` | the two ablation arms at 24 s |
| `runner_positive_control.tsv` | the runner reporting `sat` and `unsat` on files we decide — so an all-`unknown` ablation row is a finding, not a broken harness |

## Measurement

| file | what it is |
|---|---|
| `run-files.sh` | one measurement arm: `taskset -c 0-7`, per-file wall clock, `sat`/`unsat`/`unknown` only; exits non-zero if any file produced no verdict |
| `run-before-after.sh` | the A/B: the two binaries alternate **per file**, so a load change part-way through the session hits both arms equally instead of landing entirely on whichever ran second |
| `qf_uflia_reference_only_58.txt` | the sidecar population — the 58 reference-only QF_UFLIA files from `bench-results/parity-losses-20260905/QF_UFLIA.txt` (the S3 loss census), used to show nothing outside the 26 moved. Only **6** of the 58 are the wide-integer class; the other 20 of the 26 are absent because cvc5 does not decide them either |
| `qf_uflia_26_before_after.tsv`, `qf_uflia_reference_only_58_before_after.tsv` | the two A/B runs at 24 s |

## PAR-2 convention used in the report

Following `crates/axeyum-bench/src/main.rs`: a decided file contributes its own
wall-clock seconds; an undecided one contributes `2 x timeout`. At the 24 s
budget used here an `unknown` therefore scores 48 s regardless of how quickly it
was reached, so **PAR-2 cannot distinguish a fast named decline from a slow
one** — that difference is reported separately as mean wall clock.
