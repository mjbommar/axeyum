# S9 — integer literals wider than `i128`: census, ablation, and what widening buys

Lane `s9-int-wide-parser`, 2026-09-06. ADR-1702 slice 2, parity plan
[§2.3 / §4 row S9](../../plan/smt-parity-plan-2026-09-05.md).

Artifacts: [`bench-results/s9-int-wide-20260906/`](../../../bench-results/s9-int-wide-20260906/).

## 1. The census: 26 files, and the census agrees with the parser both ways

`bench-results/parity-lists/QF_UFLIA.txt` is the 200-file division listing.
[`census-wide-int-literals.py`](../../../bench-results/s9-int-wide-20260906/census-wide-int-literals.py)
scans each file for a **bare numeral** above `i128::MAX` — the exact atom shape
`crates/axeyum-smtlib/src/parse.rs` feeds to `a.parse::<i128>()` before emitting
``integer literal `…` exceeds the modeled `Int` range`` — and reports the largest
one's bit length and syntactic position.

**26 of 200.** Two magnitude classes, and every one of the 26 declares
`:status unknown`:

| max literal | files | shape |
|---:|---:|---|
| 512 bits (155 digits) | 7 | an EVM `uint256` **product** bound, `2^512`-ish |
| 258 bits (78 digits) | 19 | `2^256`-ish: `uint256` range bounds |

Position, from the TSV's head columns: the largest literal is always a
**comparison bound**, never a coefficient and never an equality constant. Its
immediate enclosing head is `>` (16 files), unary `-` (7 — a negative bound
`(- 2^255)`) or `<` (3); it is argument 1 in 23 files and argument 2 in 3; and
the enclosing application sits directly under `and` (19) or a `-` (7). Across
*all* their wide literals the modal enclosing head is `=` in 22 files, `-` in 3
and `<=` in 1 — i.e. the bulk are equalities defining `uint256`-ranged terms,
with the extremes carried by the range bounds. Wide literals are dense: 170 at
the lightest, a median of 1,054, and 11,005 in the heaviest file.

Full table:
[`qf_uflia_wide_literal_census.tsv`](../../../bench-results/s9-int-wide-20260906/qf_uflia_wide_literal_census.tsv).

**The census is a scan, so it was cross-checked against the real front door over
the whole population, not over its own hits.** `explain_corpus --list <all 200>
2000 --json` classifies exactly 26 files as `kind: wide-integer-literal`, and the
two sets agree with **zero** difference in either direction
([`census_parser_crosscheck.txt`](../../../bench-results/s9-int-wide-20260906/census_parser_crosscheck.txt)).
Running the front door only over the census's own 26 would have confirmed no
false positives and measured nothing about false negatives.

Same run, the rest of the division at a 2 s budget: 56 `sat`, 29 `unsat`, 89
`unknown`, 26 not attempted.

## 2. ADR-0376's ablation reproduces on today's tree: the widening decides 0 of 6

[ADR-0376](../09-decisions/adr-0376-integer-literals-wider-than-i128.md)
(2026-08-04) deferred this widening **on a measurement, not on cost**: with every
out-of-range literal removed from the problem, the six files cvc5 decides were
*still* `unknown`, because the binding constraint is the decision procedure
(`MAX_INT_BLAST_WIDTH = 64`, and a measured magnitude cliff between `2^24` and
`2^32`), not the literal type.

A blocker recorded a month ago is a claim about a tree that no longer exists, and
the parity plan's row S9 promises "+6 measured against cvc5", so the ablation was
re-run **before any code was written**. Two arms, each producing a file that a
perfect bignum IR could only match, never beat
([`ablate-wide-literals.py`](../../../bench-results/s9-int-wide-20260906/ablate-wide-literals.py)):

| arm | rewrite | result on the 6 |
|---|---|---|
| `rescale` | every out-of-range numeral → a distinct `2^60 + i` (170–1,617 per file) | **6/6 `unknown`** |
| `delete` | every top-level `assert` mentioning one is dropped (50–1,314 per file) | **6/6 `unknown`** |

24 s per file, `taskset -c 0-7`, release `smtcomp_cli`. The `delete` counts
reproduce ADR-0376's "50–1314 asserts each" exactly, which is the check that the
ablation is the same one. The runner is not vacuous: on four QF_UFLIA files we do
decide it reports 2 `sat` and 2 `unsat`
([`runner_positive_control.tsv`](../../../bench-results/s9-int-wide-20260906/runner_positive_control.tsv)),
so an all-`unknown` ablation row is a finding rather than a broken harness. The
ablation script also prints `NO-OP` for any file it failed to rewrite; it printed
none.

**So the parity plan's "+6 measured against cvc5" for row S9 is not supported.**
That figure is the count of these files cvc5 decides, not a measured axeyum gain;
ADR-0376 had already shown the two are different, and that finding stands. The
honest expected yield of slice 2 on QF_UFLIA is **0 decided files**, and the
value of the slice is that the 26 files stop being *not attempted* and become
first-class `unknown` on a route that can be improved — plus the representation
itself, which QF_LIA and QF_NIA and the finite-field and EVM front ends need
independently.

<!-- section 3 (the implementation) and 4 (before/after) follow below -->
