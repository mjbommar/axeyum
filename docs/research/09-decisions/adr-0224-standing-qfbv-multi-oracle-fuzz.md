# ADR-0224: Standing QF_BV multi-oracle fuzz gate

Status: accepted
Date: 2026-07-17

## Context

The consolidated Glaurung review makes strict correctness the paper's lead
contribution and asks for a generated Axeyum/Z3/neutral-solver differential
gate. The existing scalar QF_BV fuzzer already covers all public scalar
operators over 4,000 deterministic well-typed instances and replays Axeyum SAT
models, but Z3 was its only oracle and widths stopped at 32 bits. Separately,
the Glaurung study found malformed concat and extension metadata, use of an
empty model after a non-SAT result, and u64 truncation in its Z3 adapter.

Those failures do not all belong to one formula-fuzz contract. Concat/extension
metadata and post-UNSAT model use are invalid consumer states; silently
normalizing them into valid generated formulas would erase the strictness claim.
The W128 adapter failure is a valid-formula/model-lifting boundary and does
belong in a multi-oracle control.

## Decision

Extend the standing QF_BV differential test with three distinct contracts:

1. Keep all 4,000 fixed-seed well-typed formulas on the Axeyum/direct-Z3 gate,
   with original-IR replay for every Axeyum SAT model.
2. Send a deterministic 1-in-16 sample to cvc5 1.3.4. In the publication lane,
   require the external binary with `AXEYUM_REQUIRE_CVC5=1`. Treat explicit
   cvc5 `unknown` as a reported nondecision, but fail on spawn, parser, status,
   or output-protocol errors and print the complete standalone SMT-LIB script.
3. Preserve named Glaurung controls separately: strict negative construction
   tests for malformed concat/extension/constant widths; valid normalized
   concat and extension formulas; a closed SAT formula whose empty model is
   legitimate versus a contradictory UNSAT result with no model payload; and a
   W128 constant with bit 100 set through the actual linked Z3 adapter.

Do not claim that valid-formula fuzzing alone would have found Glaurung's
consumer state-machine errors. Keep those as named contract regressions.

## Evidence

At Axeyum `8fae61ad`, the required-cvc5 lane reports:

- 4,000/4,000 Axeyum/Z3 jointly decided agreements;
- 250/250 cvc5 samples decided with 250 three-way agreements;
- 1,487 Axeyum SAT models replayed on the original assertions;
- zero Unknown, timeout, crash, replay gap, process/parser failure, or verdict
  disagreement;
- all four named controls and all three strict negative controls passing.

The fail-closed distinction found a real harness defect before acceptance:
seed 352 used nonstandard `!=` in the SMT-LIB reproducer. The previous coarse
cvc5 helper hid the parser rejection as a skip. The renderer now uses
`distinct`, and the final run has zero cvc5 skips. Exact provenance and counters
are committed in
[`bench-results/qfbv-multi-oracle-fuzz-20260717/`](../../../bench-results/qfbv-multi-oracle-fuzz-20260717/README.md).

## Consequences

QF_BV generated correctness evidence is no longer Axeyum-versus-Z3 only, the
named W128 model boundary is permanent, and malformed neutral-oracle inputs
cannot inflate a zero-disagreement count. The gate remains deterministic and
keeps cvc5 out of the default dependency graph.

This closes the first standing multi-oracle fuzz tranche, not the publication
correctness program. More fixed-seed rounds, coverage accounting, Bitwuzla or a
second neutral implementation, proof-coverage measurement, and authoritative
finding parity remain open. Differential agreement is evidence, not proof.

## Alternatives

- Count every cvc5 non-verdict as a skip: rejected because it hid invalid SMT.
- Generate malformed widths and coerce them inside Axeyum: rejected because it
  weakens the consumer contract the study identifies as a contribution.
- Require cvc5 in every default build: rejected because the native-free product
  and ordinary CI must not acquire an external binary dependency.
- Replace original-term replay with three-way verdict agreement: rejected
  because shared wrong-SAT behavior must still face an independent model check.
