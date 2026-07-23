# ADR-0359: Preregister checked quantified-UF default repair

Status: proposed
Date: 2026-07-22

Implementation note (2026-07-22): the bounded repair and its focused gates are
implemented in topic commit `79a8dd21`; ADR acceptance remains withheld until
the branch-wide evidence gates below complete. The post-implementation 256-case
differential reports 178 checked Axeyum SAT results versus 111 at baseline,
zero disagreements, and canonical replay for every SAT result. The ordinary
Z3-SAT incomplete bucket fell from 96 to 39 and the resource-limited Z3-SAT
bucket from nine to zero.

## Context

Accepted ADR-0357/0358 can certify a finite-table-plus-default UF model over a
leading `Int`/`Real` universal prefix, but search currently tests only the exact
quantifier-free ground candidate. The 256-case direct-Z3 smoke differential now
adjudicates every Axeyum decline by exact reason and oracle verdict. In the
current run, 121 cases are `Unknown`: Z3 says SAT for 105, UNSAT for 11, and
Unknown for five. Of the Z3-SAT cases, 96 stop at the ordinary
"instantiation is satisfiable" boundary and nine hit the MBQI resource cap.

Seed diagnostics show the dominant SAT gap is not missing checker semantics.
Typical sources require compatible total defaults for `f` and `g`, while the
ground candidate either omits those functions or chooses defaults for ground
constraints without considering the universal. Search may repair such a
candidate, but only the existing source-bound checker may grant SAT credit.

## Decision

**Add a bounded, deterministic, untrusted repair search over only the default
results of relevant `Int`/`Real`-result UF interpretations, preserving every
existing scalar assignment and explicit function-table entry.**

The first increment is limited to the already accepted ADR-0357/0358 source
fragment and will:

- collect at most eight relevant functions, each with an `Int` or `Real`
  result;
- preserve each existing interpretation's exact signature and overriding
  entries, while allowing its default to change; synthesize a missing function
  only as a constant total interpretation with its declared signature;
- derive a stable, deduplicated candidate pool from same-sort scalar model
  values, existing UF defaults and entry results, zero, and checked `-1`/`+1`
  neighbors of those values;
- cap each pool at 32 values and the Cartesian repair search at 256 complete
  candidates; overflow or any unsupported shape declines; and
- attach certificates and return SAT only after the independent finite-profile
  checker accepts every original universal and canonical `check_model` accepts
  the exact original assertion sequence.

Search order, values, and success are not evidence. The returned function model
and source-bound certificates remain the complete checkable artifact. If no
candidate passes, the existing instantiation and E-matching behavior is
unchanged.

## Evidence gates

Acceptance requires:

1. Missing one- and two-function interpretations are completed to checked SAT
   for representative universal inequalities and disequalities.
2. Existing table entries and ground constraints are preserved while defaults
   change; a repair that would alter an explicit point is rejected.
3. Strict inequalities exercise checked predecessor/successor candidates for
   both integer and real results.
4. Unsupported result sorts, function/pool/product caps, arithmetic overflow,
   false universals, and tampered repaired models decline without changing the
   UNSAT route.
5. The adjudicated 256-case direct-Z3 sweep has zero disagreement, every SAT
   result replays, and the Z3-SAT ordinary-incomplete bucket decreases from the
   preregistered 96-case baseline.
6. Focused model/evidence tests, solver Clippy and rustdoc, workspace tests,
   foundational resources, parity, links, and lane gates are green.

## Alternatives

- **Trust a repair assignment.** Rejected: search completeness and correctness
  are irrelevant unless the exact source checker accepts the resulting model.
- **Rewrite explicit table entries.** Deferred: this expands the search and can
  disturb ground facts. Default-only repair is independently useful and has a
  much smaller state space.
- **Search arbitrary arithmetic terms for defaults.** Deferred: the bounded
  value pool tests the measured need without introducing a term synthesizer.
- **Increase MBQI rounds first.** Rejected as the primary response: 96 of 105
  oracle-SAT declines are ordinary stable candidates, not the resource bucket.

## Consequences

This can turn a large measured class of honest Unknowns into checked SAT while
leaving the trust boundary unchanged. It does not claim complete MBQI, repair
explicit table entries, solve the 11 oracle-UNSAT declines, widen source
admission, or provide Lean SAT reconstruction.
