# Full-cvc5 QF_BV multi-oracle differential fuzz

- Date: 2026-07-17
- Axeyum revision: `cf37d2693ee87c384c3c923f2356d45603d59a9c`
- Report SHA-256:
  `27d54610a02f410561013687ab121391ae9db7abfd3d7ff0440b10ed2bdf64fd`
- Generator: fixed seeds 0 through 3,999
- Neutral policy: every generated instance must receive a concrete cvc5 verdict
- Replay policy: every Axeyum SAT model must satisfy every original assertion

This is the exhaustive-neutral continuation of ADR-0224's sampled standing
gate. All 4,000 generated formulas decide in Axeyum, direct Z3, and cvc5, and
all 4,000 verdicts agree three ways. There are zero Unknowns, timeouts, crashes,
parser/process failures, replay gaps, or disagreements. All 1,487 Axeyum SAT
models replay against the original IR assertions.

Coverage is now an executable acceptance condition rather than a prose claim.
The fixed sweep hits all declared random widths (1, 4, 8, 16, and 32 bits) and
all 35 required generator classes: variables/constants; Boolean connectives;
all ten equality, unsigned, and signed comparisons; every scalar bit-vector
arithmetic, division/remainder, bitwise, and shift operator; and concat,
extract, zero extension, and sign extension. A missing width or operator fails
the test.

The ordinary external-oracle lane remains a 1-in-16 sample to keep routine test
cost bounded. The publication command sets the stride to one and requires all
4,000 cvc5 rows to decide. Named strict Glaurung controls, including the linked
W128 adapter boundary, also pass at the recorded revision; they remain separate
because malformed consumer metadata and post-UNSAT model use are not valid
well-typed formula states.

Exact counters, the ordered coverage inventory, limits, revisions, and binary
hashes are in [`report.json`](report.json). This is broad differential evidence,
not a formal correctness proof and not an authoritative finding-parity result.
