# ADR-0237: Independent and edge-directed QF_BV four-oracle fuzzing

Status: proposed
Date: 2026-07-18

## Context

ADR-0224/0225 established one deterministic 4,000-formula seed round with
Axeyum, direct Z3, and cvc5 agreement, original-model replay, and executable
operator/width presence. The reviewer checklist correctly identifies what that
does not establish: seed independence, frequency-accounted semantic corners,
or agreement with another neutral implementation. Repeating seeds 0..4,000 or
reporting only that each operator occurred would not close those gaps.

This ADR preregisters the untouched publication ranges before inspecting their
full results. A 256-row engineering pilot used seeds 4,000..4,256 to validate
the mechanism and is excluded from the accepted evidence.

## Decision

Run exactly three disjoint 4,000-row rounds through Axeyum, direct Z3, cvc5
1.3.4, and Bitwuzla 0.9.1:

| Round | Generator | Seed range |
|---|---|---:|
| `uniform-a` | `uniform-v1` | 1,000,000..1,004,000 |
| `uniform-b` | `uniform-v1` | 2,000,000..2,004,000 |
| `edge-c` | `edge-v1` | 3,000,000..3,004,000 |

Require every row to decide and agree in all four engines, require every
Axeyum SAT model to replay on the original IR, fail closed on external process
or parser failures, and retain zero-result classes separately from failures.
Use an explicit 600,000 ms per-row cap for Axeyum and each external oracle. The
Axeyum cap is an operational worker bound rather than a timeout passed into the
pure-Rust search; the all-decided assertion remains the admission rule.
The two uniform rounds preserve ADR-0225's generator byte-for-byte for a given
seed. The edge round adds one rotating true control after the random formula;
it must observe nonzero instance frequencies for all declared constant,
division/remainder-by-zero, signed-overflow, over-shift, extraction-boundary,
zero-extension, sign-extension, and one-bit-concat categories.

Use
[`scripts/run-qfbv-independent-oracle-rounds.sh`](../../../scripts/run-qfbv-independent-oracle-rounds.sh)
as the executable protocol. The runner fixes the ranges, requires stride one
for both external oracles, hashes and versions both binaries, writes one JSON
report and raw log per round, and refuses a nonempty output directory.

## Evidence

Pending the preregistered run. The excluded engineering pilot decided and
agreed on all 256 rows in all four engines, replayed all 97 SAT models, and
observed all 14 required edge categories. Its purpose was to validate the
runner and telemetry, not to support the final claim.

The first full attempt inherited the routine 5,000 ms Axeyum worker cap because
the proposed protocol failed to state it explicitly. `uniform-a` reached 3,999
four-way agreements, then failed closed on reproducible seed 1,002,261; rounds
B and C did not run and no success JSON was written. The raw log and environment
are retained under
`bench-results/qfbv-four-oracle-independent-20260718/`. A focused unchanged-seed
diagnostic decides the same formula under 30,000 ms. Before rerunning any full
range, this amendment fixes that cap, adds exact nondecision seed/reproducer
telemetry, and adds a direct all-decided assertion. The formulas and ranges are
unchanged.

The second full attempt accepted that amendment and completed `uniform-a` at
4,000/4,000 four-way agreement, including seed 1,002,261, but inherited the
existing 2,000 ms external-oracle limit. It failed closed at `uniform-b` seed
2,003,009 when cvc5 1.3.4 exhausted that limit and aborted; `edge-c` did not
run. The exact SMT-LIB script reproduces the 2,000 ms abort and returns `sat`
under 30,000 ms; Bitwuzla returns `sat`. This second pre-rerun amendment applies
the same explicit 30,000 ms cap to all engines and records both caps in JSON.
It also canonicalizes the report directory before Cargo changes the test
working directory. Again, no formula or seed changes.

The third full attempt completed both uniform rounds at 4,000/4,000, then
failed closed on `edge-c` seed 3,000,881 when Axeyum exceeded 30,000 ms. A
120,000 ms focused rerun also timed out. Under 600,000 ms, the unchanged formula
decides `unsat` in all engines: Axeyum finishes between 120 and 600 seconds,
direct Z3 in 25.225 seconds isolated, cvc5 in 41.67 seconds, and Bitwuzla in
12.62 seconds. A loaded combined diagnostic also showed Z3 narrowly exceeding
30 seconds after the long Axeyum solve. The final pre-rerun amendment therefore
uses the same 600,000 ms correctness bound for every engine. This is not a
performance cell, and no formula or seed changes.

## Alternatives

- Extend the old range contiguously from seed 4,000: rejected because the
  engineering pilot already inspected part of that range.
- Count only operator presence: rejected because it does not show SMT-LIB
  totality corners were generated.
- Replace cvc5 with Bitwuzla: rejected because four-way agreement is stronger
  and avoids changing the already accepted neutral baseline.
- Make `edge-v1` the routine default: rejected because it would silently change
  ADR-0224/0225 seed identity and make historical reproduction ambiguous.
- Treat external `unknown` or malformed output as a skip in this campaign:
  rejected because an all-decided publication result must fail closed.

## Consequences

If accepted, this campaign can support a bounded claim of four-engine verdict
agreement and measured semantic-corner coverage over 12,000 new formulas. It
will not prove QF_BV completeness, cover arbitrary term depth/width, or replace
consumer-state regressions, real Glaurung proof manifests, and authoritative
finding tests.
