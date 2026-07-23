# ADR-0364: Preregister profile-guided quantified-UF model completion

Status: proposed
Date: 2026-07-23

## Context

ADR-0357/0358 independently certify finite-profile models for the
almost-uninterpreted quantified fragment. ADR-0359 through ADR-0363 improve
untrusted candidate generation without changing that evidence boundary. The
frozen 256-case quantified-UFLIA differential now has 215 checked SAT, 24
UNSAT, and 17 Unknown results. Exactly three Unknowns remain ordinary Z3-SAT.

The exact
[profile-completion measurement](../../plan/quantified-uflia-profile-guided-model-completion-measurement-2026-07-23.md)
shows that these cases require explicit table structure or a source-defined
total function. Default-only search cannot express them. A bounded CEGIS loop
over exact finite-profile counterexamples closes all three, plus one
independently certified case where Z3 times out, under the original shared
deadline.

## Decision

**After every established MBQI, E-matching, and ADR-0361 route declines, run one
SAT-only, single-`Int`-binder finite-profile completion loop under the remaining
caller-owned deadline. Use exact source definitions and checker-derived
falsifying profiles only as search hints; accept solely through independent
finite-profile certification and canonical full-source replay.**

The implementation will:

- run only for one top-level `Int` universal in the already accepted
  almost-uninterpreted finite-profile fragment; multiple universals, multiple
  binders, `Real`, non-value function storage, and unsupported signatures
  decline;
- rebuild each candidate from the original quantifier-free ground assertions
  plus only accumulated exact instances of the untouched universal body;
- complete an absent source-relevant `Int`-result function with a zero default
  only to make the untrusted candidate evaluable; malformed or incompatible
  existing interpretations decline;
- recognize only top-level conjunctive equalities whose one side is exactly
  unary `f(binder)` and whose other side is binder-independent, evaluate that
  side under the candidate, and propose a total constant `Int -> Int`
  interpretation for `f`; this proposal may replace stale candidate entries,
  but it is never evidence;
- derive the next falsifier from the exact binder argument positions, existing
  finite table keys, and alternating `0, 1, -1, 2, -2, ...` fresh-value rule
  shared with the independent checker;
- add at most one new exact source instance per round, use stable order, and cap
  the loop at 32 rounds and 32 accumulated instances;
- derive every inner QF timeout from the original outer deadline and check that
  deadline before and after each solve;
- decline on inner UNSAT, Unknown, error, duplicate instance, missing
  interpretation, unsupported profile, absent falsifier, cap exhaustion, or
  deadline expiry; no inner non-SAT result transfers; and
- return SAT only after every original universal receives the existing
  independent finite-profile certificate and canonical `check_model` accepts
  the exact original assertion sequence.

The loop is placed after ADR-0361 so no earlier SAT/UNSAT decision or search
priority changes. It uses only remaining time and returns the established
E-matching Unknown on decline. No public evidence type, checker admission,
source fragment, UNSAT route, value pool, default Cartesian cap, or scalar
completion cap changes.

## Evidence gates

Acceptance requires:

1. Focused tests freeze exact direct-binder-position discovery, alternating
   fresh representatives, source-body instantiation, and exclusion of
   interpreted-position binders, multiple binders/universals, non-`Int`
   signatures, malformed storage, and nonconjunctive/nondefinitional shapes.
2. Exact definitional completion clears stale entries only for
   `f(binder) = ground_term`, preserves unrelated functions/scalars, and fails
   closed when the ground side cannot be evaluated; tampered proposals fail
   certificate or full replay.
3. Inner UNSAT/Unknown/error and expired-deadline controls decline without
   transfer, and the exact 32-round/32-instance boundary is tested at and one
   over the cap.
4. Seeds 122, 175, 182, and 226 return independently checked and exactly
   replayed SAT at the measured 1/0/1/2 rounds and 1/0/1/2 instances.
5. ADR-0360 seed 145, ADR-0361 seeds 23/231, ADR-0362 seed 111, ADR-0363 seeds
   30/32/70/150/242, and all prior SAT/UNSAT outcomes remain unchanged.
6. The frozen production differential returns exactly 219 SAT, 24 UNSAT, and
   13 Unknown with 219/219 SAT replay, zero error/disagreement, no ordinary
   Z3-SAT residual, and at least 235 jointly decided agreements. Oracle timeout
   variation may increase the joint count but may not weaken an Axeyum/replay
   invariant.
7. Solver Clippy, strict rustdoc, focused/full solver tests, branch-owned
   documentation, and proportional repository gates pass. Cross-lane retained
   evidence remains separately reported and is never rewritten here.

## Alternatives

- **Raise ADR-0363's 256-default-product cap.** Rejected: uncapped search over
  its fixed seed-122 pool still finds no model; the missing information is table
  structure and dependent evaluation, not only one extra Cartesian cell.
- **Blindly seed sixteen integer instances.** Rejected by measurement: it
  quickly closes seed 122 but makes seeds 175 and 182 overfit table entries; one
  exhausts the round cap and the other times out.
- **Rewrite arbitrary explicit entries.** Rejected: only an exact source total
  definition may propose a constant replacement, and final replay remains
  authoritative.
- **Run before established MBQI/E-matching routes or grant a fresh timeout.**
  Rejected: the mechanism is additive only when it uses leftover time after
  prior decisions have had their existing opportunity.
- **Transfer inner UNSAT.** Rejected: this is a SAT-only candidate generator;
  no new UNSAT evidence route is introduced.
- **Use a Z3 model or require Z3 SAT.** Rejected: seed 226 is independently
  certified while Z3 times out, and production search never consumes oracle
  data.

## Consequences

The expected frozen differential moves from 215 to exactly 219 checked SAT
models, preserves 24 UNSAT results, reduces Unknown from 17 to 13, and removes
the final ordinary Z3-SAT residuals. The mechanism adds bounded table/model
search, not trust: the existing finite-profile checker and canonical source
replay remain the only SAT authority. General function synthesis, multiple
universal coordination, multi-binder/Real profiles, function-valued models,
proof reconstruction, and any UNSAT transfer remain open.
