# ADR-0358: Preregister multi-binder finite-profile quantified-UF models

Status: proposed
Date: 2026-07-22

## Context

Accepted ADR-0357 gives Axeyum a checked SAT result for one top-level
almost-uninterpreted `Int` or `Real` universal. The checker derives all values
that can select a finite UF-table entry at the binder's exact argument
positions, adds one fresh default representative, and evaluates the untouched
body at every representative.

The proof generalizes directly to a leading block of universal binders, but the
implementation currently rejects that source because the inner `forall` is
classified as a nested quantifier. This excludes ordinary relations such as
`forall x y. f(x, y) >= 0`, even when a finite-table model makes the complete
Cartesian proof small.

## Decision

**Extend the ADR-0357 checker to one nonempty leading `forall` block and check
the Cartesian product of independently derived binder representatives, while
retaining an explicit binder cap and the existing 4,096 total-profile cap.**

The accepted shape will require:

- one top-level assertion whose leading prefix contains one through 16 distinct
  `Int` or `Real` universal binders;
- a quantifier-free matrix after that complete prefix;
- every binder to occur at least once, only as a direct argument of an
  uninterpreted-function application;
- total, signature-matching finite-table-plus-default interpretations for all
  relevant functions; and
- a checked Cartesian product of at most 4,096 representative tuples.

For each binder independently, the checker re-derives the exact function
argument positions occupied by that binder, collects the matching components
from every model table key, and adds one same-sort fresh representative outside
that finite set. It checks the Cartesian product of those sets against the
untouched matrix. Product overflow, duplicate binders, a missing binder
occurrence, a non-leading or existential quantifier, unsupported sorts, model
signature drift, or any failed evaluation declines.

The certificate remains minimal: its exact assertion binds the complete prefix
and matrix, while its existing redundant binder field names the outermost
binder. Search does not provide representative tuples or coverage metadata.

The first search-side widening is SAT-only. The MBQI front door may obtain one
quantifier-free ground candidate and attach the multi-binder certificate only
after canonical replay succeeds. If certification declines, existing
E-matching handles refutation; this increment does not add an unreviewed
multi-variable instantiation heuristic.

## Evidence gates

Acceptance requires all of the following:

1. Two-binder integer and mixed integer/real positive cases return SAT through
   `solve`, carry one source certificate, and pass canonical model and SAT
   evidence replay.
2. A binary function test distinguishes real diagonal/off-diagonal Cartesian
   profiles and rejects a violation reachable only at one table-key tuple.
3. Independent per-binder representative sets are used; values from the wrong
   argument position cannot fabricate coverage.
4. Duplicate binders, vacuous binders, existential or non-leading quantifiers,
   interpreted occurrences, unsupported sorts, missing functions, bad
   signatures, product overflow, and tampered certificates reject.
5. Existing one-binder SAT, UNSAT, out-of-fragment, tamper, and cap behavior is
   unchanged.
6. Focused model/evidence/search suites, direct-Z3 quantified differential,
   workspace Clippy and rustdoc, foundational resources, and links are green.

## Alternatives

- **Trust search-generated tuples.** Rejected: omission of one Cartesian point
  would make an infinite-domain SAT result unsound.
- **Use one union of values for every binder.** Rejected: it performs avoidable
  work, obscures mixed-sort handling, and loses the exact argument-position
  proof.
- **Add multi-variable counterexample search simultaneously.** Deferred: the
  checked SAT capability is independent, while refutation already has the
  E-matching fallback.
- **Admit arbitrary nested quantifiers.** Rejected: alternation and quantifiers
  below the matrix require different semantics and evidence.

## Consequences

Axeyum can certify common multi-argument UF models over infinite scalar domains
without sampling or trusting the MBQI searcher. Runtime and memory remain
deterministically bounded by 16 binders and 4,096 checked tuples. Larger
products, vacuous prefixes, existential alternation, interpreted binder
expressions, uninterpreted carrier sorts, model repair, serialization, and Lean
reconstruction remain honest follow-ups.
