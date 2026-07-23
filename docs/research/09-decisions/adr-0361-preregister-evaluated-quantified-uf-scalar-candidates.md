# ADR-0361: Preregister evaluated quantified-UF scalar candidates

Status: proposed
Date: 2026-07-23

## Context

ADR-0360 implements a SAT-only, replay-checked search over at most two free
`Int` symbols for the almost-uninterpreted quantified-UF fragment. On the frozen
256-case quantified-UFLIA differential it reaches 225 jointly decided cases,
with 207 checked SAT models, and leaves eleven ordinary Z3-SAT cases Unknown.

The ADR-0360 value pool contains zero, initial scalar assignments, exact source
integer constants, and their checked immediate neighbours. The initial
quantifier-free candidate already contains additional deterministic integer
information that the pool discards: UF default/override results and values of
ground integer source subterms under that same candidate. Those values are
untrusted model-generation hints, just like the existing scalar assignments.

A retained fixed-query probe over the eleven residual seeds adds only those
candidate values before applying the existing neighbour closure. Under the
unchanged 16-value and 256-tuple caps, it found three models:

| Seed | Exact free Ints | Closed pool | Tuples | Checked assignment |
|---:|---:|---:|---:|---|
| 23 | 2 | 13 | 169 | `[-4, -4]` |
| 231 | 2 | 12 | 144 | `[-10, -10]` |

Production-path validation then corrected the boundary: seeds 23 and 231 pass
the actual one-shot candidate-certification path, while seed 111 succeeds only
when the probe recursively re-enters the complete MBQI loop with its fixing.
ADR-0361 does not add that recursive search. The exact production gate is
therefore **two** additional models, not three. Both returned models pass
canonical replay against the original assertions without their temporary
equalities. The other nine seeds remain Unknown. In particular, seed 175
produces 23 values and therefore declines without truncation; seeds 150 and 242
contain no exact-source free `Int` and remain outside the search.

## Decision

**After the established MBQI and E-matching routes both decline, retry only
ADR-0360's SAT candidate search with integer results already present in the
initial ground candidate and evaluable exact-source integer subterms. Keep
every resource and evidence boundary unchanged.**

The implementation will:

- add every `Int` default and overriding result from the initial model's UF
  interpretations;
- traverse the exact assertion DAG deterministically and add the value of an
  `Int` term only when ordinary ground evaluation succeeds under the initial
  candidate; terms depending on a universal binder naturally fail evaluation
  and contribute nothing;
- retain zero and initial scalar values, deduplicate with stable ordering, then
  apply the existing checked predecessor/successor closure exactly once;
- retain the existing exact-source one/two-free-`Int`, 16-value, 256-tuple, and
  shared-deadline gates, declining rather than truncating on any overflow; and
- save the initial ground candidate, run ordinary ADR-0360 completion, MBQI,
  and E-matching first, and spend only the remaining shared deadline on the
  evaluated pool after all of those established routes decline; and
- continue treating all values and temporary equalities as search hints. Only
  ADR-0357/0358 certification, optional ADR-0359 repair, and canonical replay
  of the exact original assertion sequence may return SAT.

Function arguments are not added merely because they occur in a model table;
they are already covered when they are source-evaluable terms. Non-`Int`
values, evaluation failures, absent functions, and malformed interpretations
do not widen or fail the ordinary MBQI path.

## Evidence gates

Acceptance requires:

1. Focused tests prove deterministic collection of scalar assignments, UF
   default/override results, and evaluable exact-source terms, while excluding
   binder-dependent and non-`Int` values.
2. The two production-measured seeds become checked SAT with the exact closed
   pool sizes, tuple counts, and assignments above under the existing caps;
   seed 111 remains Unknown unless a separately preregistered recursive search
   is added.
3. Seed 175 declines on complete-pool overflow; zero-symbol seeds 150/242 and
   the other unsupported residual shapes remain honest Unknowns.
4. Temporary-fixing failure cannot transfer to the original query, and every
   accepted model and quantified-UF certificate replays against the unfixed
   source. Tampered scalar/function values or certificates reject.
5. The normal 256-case direct-Z3 differential has zero disagreements, replays
   every Axeyum SAT model, and reduces the ordinary Z3-SAT residual by at least
   the measured two cases without changing any prior SAT or UNSAT result.
6. Solver Clippy/rustdoc, focused and full solver tests, complementary workspace
   tests, foundational resources, profiles, recovery, parity, and links pass.

## Implementation evidence

Commit `471738aa` implements the decision without changing any public evidence
type or resource cap. The evaluated retry is deliberately last: the solver
first runs the existing ADR-0360 pool, ordinary MBQI, and E-matching, then uses
only the remaining shared deadline. This preserves seed 145, which regressed to
a resource-limit Unknown when an intermediate implementation ran the expanded
pool before the established routes.

Focused tests cover deterministic value collection, explicit rejection of
binder-dependent source terms even when the model assigns the binder, checked
SAT for seeds 23 and 231, and preservation of seed 145. The frozen 256-case
production differential reaches 227 jointly decided agreements, 209 Axeyum SAT,
24 Axeyum UNSAT, and 23 Axeyum Unknown, with 209/209 SAT replay and no error or
disagreement. Its ordinary-incomplete Z3-SAT remainder is exactly
`30, 32, 70, 111, 122, 150, 175, 182, 242`; no previous SAT or UNSAT result is
lost. Acceptance remains pending until the complete branch-wide gate finishes.

## Alternatives

- **Increase the value/tuple caps.** Rejected: every measured success is already
  below 16/256. Seed 175's 23-value pool is evidence to decline, not to widen.
- **Recursively rerun MBQI under every fixing.** Deferred: it explains the
  exploratory seed-111 result but is a distinct, more expensive search with
  recursion and termination obligations.
- **Add arbitrary arithmetic synthesis.** Deferred: exact candidate/source
  values close two cases without introducing a new synthesis language.
- **Trust initial UF values as evidence.** Rejected: they remain search hints.
  The finite-profile checker and original-query replay remain authoritative.
- **Search when no exact-source free scalar exists.** Rejected: that is UF
  interpretation repair, a separate mechanism from scalar completion.

## Consequences

This increment improves model generation without changing the trusted checker,
the public evidence format, any UNSAT route, or the resource envelope. It does
not address the nine residual cases, free `Real` symbols, more than two free
scalars, general function synthesis, or complete MBQI.
