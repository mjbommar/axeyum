# Checked multi-binder quantified-UF models

Status: implemented; final branch-wide gate pending
Date: 2026-07-22
Decision: [ADR-0358](../research/09-decisions/adr-0358-preregister-multi-binder-finite-profile-quantified-uf-models.md)
Owner: solver/engine lane in `agent/smtcomp/full-library-resume`

## Outcome

The accepted ADR-0357 one-binder finite-profile proof now extends to one
leading block of at most 16 distinct `Int`/`Real` universal binders. The checker
derives a separate representative set for every binder from that binder's exact
UF argument positions, adds one fresh default representative per binder, and
evaluates the untouched quantifier-free matrix over their complete Cartesian
product. The existing 4,096 cap now bounds total tuples rather than one
binder's list.

This is public functionality, not search-side sampling. A two-binder integer or
mixed integer/real candidate returned by `solve` carries the exact-source
certificate and passes both canonical `check_model` and `Evidence::Sat::check`.
The certificate still stores only the exact assertion and redundant outer
binder: the checker independently reconstructs the full prefix and all profile
sets.

## Search and fallback

The existing single-binder MBQI refutation loop is unchanged. When a query has
a multi-binder leading prefix, the front door obtains one quantifier-free ground
candidate and attempts the Cartesian certificate. An accepted candidate returns
SAT only after original-query replay. A declined candidate immediately returns
to the existing E-matching route; no new multi-variable refutation heuristic or
search tuple becomes trusted evidence.

A focused conflicting-point test exercises that boundary: certification rejects
the candidate and E-matching proves the original two-binder query UNSAT.

## Fail-closed boundaries

The checker declines:

- more than 16 binders or more than 4,096 Cartesian tuples;
- duplicate, vacuous, Bool/BV, or uninterpreted-sort binders;
- existential or other non-leading quantifiers;
- any interpreted binder occurrence;
- missing, scalar-storage, or signature-mismatched relevant functions;
- a non-Boolean or false matrix evaluation; and
- stale, extra, or wrong-outer-binder certificates through the inherited model
  contract.

## Completed focused gates

- MBQI model finder: 18/18, including integer and mixed-sort front-door SAT,
  Cartesian table-point rejection, fallback UNSAT, malformed prefixes, and both
  caps;
- solver library: 894/894;
- evidence: 69/69;
- instantiation: 15/15;
- capability/support ledgers: 2/2 and 12/12;
- solver all-target/all-feature warning-denied Clippy;
- established 256-case one-binder direct-Z3 regression: zero disagreement and
  every Axeyum SAT result replayed; and
- new two-binder direct-Z3 matrix: 64/64 agreements, split 32 SAT / 32 UNSAT,
  with every Axeyum SAT result passing canonical source replay.

Workspace-wide tests, strict rustdoc, foundational resources, parity/link
checks, and lane provenance gates remain before ADR acceptance.

## Deliberate next boundary

This increment does not add multi-variable MBQI counterexample search, vacuous
prefix elimination, existential alternation, interpreted binder expressions,
uninterpreted carrier sorts, arbitrary model repair, serialized certificates,
or Lean SAT reconstruction. After the branch-wide gates, measure whether
SAT-only ground candidates leave enough genuinely satisfiable profiles unknown
to justify a separately checked model-repair proposal.
