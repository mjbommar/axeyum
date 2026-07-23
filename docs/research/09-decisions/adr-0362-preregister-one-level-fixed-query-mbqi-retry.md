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

**Immediately after the initial ground candidate fails direct certification,
permit one recursion-guarded MBQI pass under the first ordered value in
ADR-0361's complete pool for exactly one relevant source `Int`. If it declines,
continue ADR-0360, ordinary MBQI, E-matching, and ADR-0361 unchanged. Treat the
equality as search guidance and accept only replay-clean SAT against the exact
unfixed original assertions.**

The implementation will:

- reuse `mbqi_free_int_symbols` and decline unless exactly one relevant source
  symbol exists and has sort `Int`;
- reuse ADR-0361's evaluated pool, including deterministic ordering, checked
  neighbour closure, and the existing 16-value non-truncating cap;
- run only after the initial ground candidate fails direct finite-profile
  certification and before ADR-0360's complete candidate sweep;
- select only the first ordered evaluated value and permit at most one inner
  MBQI invocation before continuing ADR-0361's complete one-shot sweep;
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

The originally proposed post-ADR-0361 placement was corrected before an
implementation commit. Focused tests showed that ADR-0360, ordinary MBQI, or
E-matching can consume the caller's remaining deadline, leaving no budget for a
later inner pass. The first-candidate-only placement immediately after failed
initial certification is executable under the same deadline, matches seed
111's measured first-candidate success, and is narrower than rerunning MBQI for
all values. Its frozen 256-case prototype reaches 228/228 agreement and 210/210
SAT replay with no prior decision lost; seed 145 remains checked SAT.

## Evidence gates

Acceptance requires:

1. A focused seed-111 regression returns checked SAT at the measured first
   candidate while canonical replay succeeds on the unfixed query.
2. A recursion control proves the inner call cannot enter fixed-query retry.
3. A fixed-query UNSAT control is ignored rather than transferred, and tampered
   returned scalar/function data fails original-query replay.
4. Zero-symbol, multiple-symbol, pool-overflow, and first-candidate failures
   continue into the unchanged evaluated sweep and remain honest Unknowns when
   every established route declines.
5. The normal 256-case differential reaches at least the measured 228 jointly
   decided agreements and 210/210 SAT replay with no error, disagreement, or
   previously decided result lost.
6. Focused and full solver tests, solver Clippy/rustdoc, complementary workspace
   tests, foundational resources, profiles, recovery, reflection, parity, and
   links pass, subject to explicitly recorded unrelated branch blockers.

## Alternatives

- **Call the public MBQI entry recursively without a guard.** Rejected: the
  implementation would have only a time bound, not a structural depth bound.
- **Run the inner loop for every scalar value or two free scalars.** Deferred:
  up to 16 or 256 complete MBQI
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

## Implementation evidence

Commit `f380d1b3` implements the decision with a private guarded entry and one
first-value helper. The inner invocation passes `false`, making retry depth
structurally one; its timeout is the outer remaining deadline. Only inner SAT
that passes canonical replay on the unfixed assertions can return. Focused
controls cover disabled retry, fixed-query SAT, unfixed replay, exact seed 111 at
`-5`, and rejection of inner UNSAT/Unknown.

The frozen production differential passes at 228/228 jointly decided
agreements, 210 Axeyum SAT, 24 Axeyum UNSAT, 22 Axeyum Unknown, 210/210 SAT
replay, and zero error/disagreement. Seeds 23, 231, and 145 remain checked SAT;
the ordinary Z3-SAT residual is exactly
`30, 32, 70, 122, 150, 175, 182, 242`. Solver Clippy, strict rustdoc, and one
uninterrupted CI-mode full package run pass, including 904 library tests, every
non-ignored integration test, and two doctests. The decision remains proposed
pending the unchanged cross-lane Lean parity attribution blocker recorded in
the workstream status.
