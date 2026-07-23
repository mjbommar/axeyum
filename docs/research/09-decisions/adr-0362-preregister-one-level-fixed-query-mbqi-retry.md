# ADR-0362: Preregister one-level fixed-query MBQI retry

Status: proposed
Date: 2026-07-23

## Context

ADR-0361 leaves nine ordinary Z3-SAT cases Unknown on the frozen 256-case
quantified-UFLIA differential. Its one-shot scalar completion already supplies
the candidate values to quantifier-free model generation and independently
certifies the resulting finite UF profile. Replacing those scalars with values
from a complete Z3 model does not close any of the nine residual cases.

One retained diagnostic identifies a different bounded gap. Seed 111 has one
relevant exact-source `Int`, an 11-value ADR-0361 pool, and succeeds at the first
ordered candidate, `-5`, only when the ordinary MBQI loop runs once under that
temporary fixing. The returned model replays against the original assertions
after removing the fixing. Across all nine residual seeds the diagnostic checks
45 candidate queries and finds no other model; three pools overflow, two seeds
have no relevant source scalar, and three bounded searches exhaust.

The diagnostic recursively calls the public entry. That is useful measurement
but not a production termination contract: a nested call could otherwise start
the same fixed-query retry again.

## Decision

**After every established outer route declines, permit one recursion-guarded
MBQI pass under each value in ADR-0361's complete pool for exactly one relevant
source `Int`. Treat the equality as search guidance and accept only replay-clean
SAT against the exact unfixed original assertions.**

The implementation will:

- reuse `mbqi_free_int_symbols` and decline unless exactly one relevant source
  symbol exists and has sort `Int`;
- reuse ADR-0361's evaluated pool, including deterministic ordering, checked
  neighbour closure, and the existing 16-value non-truncating cap;
- run only after ADR-0360 completion, ordinary MBQI, E-matching, and ADR-0361
  one-shot evaluated completion decline;
- derive every inner timeout from the outer shared deadline;
- call an internal MBQI entry with fixed-query retry disabled, making recursive
  retry depth structurally at most one;
- ignore inner `Unsat`, because unsatisfiability under a temporary equality does
  not transfer to the original query, and ignore inner `Unknown`; and
- return inner `Sat` only after canonical `check_model` validates the returned
  model against the exact original assertions without the fixing.

This changes no public evidence type, checker, UNSAT route, value cap, tuple cap,
or source-fragment admission. The inner loop may use ordinary checked repair and
finite-profile certification; none of its search trace is evidence.

## Evidence gates

Acceptance requires:

1. A focused seed-111 regression returns checked SAT at the measured first
   candidate while canonical replay succeeds on the unfixed query.
2. A recursion control proves the inner call cannot enter fixed-query retry.
3. A fixed-query UNSAT control is ignored rather than transferred, and tampered
   returned scalar/function data fails original-query replay.
4. Zero-symbol, multiple-symbol, pool-overflow, and exhausted searches remain
   honest Unknowns under the unchanged shared deadline.
5. The normal 256-case differential reaches at least the measured 228 jointly
   decided agreements and 210/210 SAT replay with no error, disagreement, or
   previously decided result lost.
6. Focused and full solver tests, solver Clippy/rustdoc, complementary workspace
   tests, foundational resources, profiles, recovery, reflection, parity, and
   links pass, subject to explicitly recorded unrelated branch blockers.

## Alternatives

- **Call the public MBQI entry recursively without a guard.** Rejected: the
  implementation would have only a time bound, not a structural depth bound.
- **Run the inner loop for two free scalars.** Deferred: up to 256 complete MBQI
  attempts has no measured residual payoff and materially widens work.
- **Raise the 16-value cap.** Rejected: seed 111 succeeds within the existing
  pool; overflow cases require separate measurement.
- **Trust fixed-query UNSAT.** Rejected: adding `y = c` strengthens the query,
  so its refutation does not establish the unfixed query is UNSAT.
- **Add general UF synthesis.** Deferred: one ordinary guarded MBQI pass closes
  the measured case without a new synthesis language or evidence form.

## Consequences

The expected frozen differential moves from 227 to 228 jointly decided cases
and from 209 to 210 checked SAT models. The other eight residual cases remain
separate. The mechanism adds bounded search depth, not proof power: the same
finite-profile checker and exact original-query replay remain authoritative.
