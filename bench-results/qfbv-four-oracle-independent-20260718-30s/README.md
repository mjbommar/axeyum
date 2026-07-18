# ADR-0237 second full attempt (rejected)

This directory preserves the fail-closed second attempt at ADR-0237. It is
**not** the accepted success artifact.

- Axeyum commit: `3034a7c4`
- Formula ranges: unchanged from ADR-0237
- Axeyum worker cap: 30,000 ms
- Z3/cvc5/Bitwuzla cap: inherited 2,000 ms
- `uniform-a`: 4,000/4,000 four-way agreements, 1,432/1,432 SAT replays,
  zero nondecisions or failures
- `uniform-b`: failed closed at seed 2,003,009 when cvc5 1.3.4 exhausted its
  2,000 ms limit and aborted; Bitwuzla was not invoked after that fail-closed
  event; `edge-c` did not run

`uniform-a.json` is a valid successful round report but this attempt as a whole
is rejected. `uniform-b.log` and `cvc5-timeout-seed-2003009.smt2` preserve the
exact failure. Direct unchanged-formula diagnostics reproduce the cvc5 abort at
2,000 ms and return `sat` under 30,000 ms; Bitwuzla 0.9.1 returns `sat` as well.
The runner also exposed that a relative report directory was interpreted from
Cargo's crate working directory; the JSON was recovered byte-for-byte and the
runner now canonicalizes the output path before invoking Cargo.

The next protocol amendment keeps every formula and seed fixed, applies the
same explicit 30,000 ms cap to all four engines, and records that cap in the
JSON report.
