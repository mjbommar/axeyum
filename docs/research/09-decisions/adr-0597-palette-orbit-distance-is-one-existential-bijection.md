# ADR-0597: Palette-orbit distance is one existential bijection

Status: accepted
Date: 2026-08-27

## Context

ADR-0595's repair neighborhood measures labelled Hamming distance. That is useful for local search,
but it is not invariant under renaming interchangeable colours. The first checked 405-point Rado
radius-22 refutation therefore could not be stated as a property of the colouring orbit. Running one
formula per permutation scales as `k!`, spreads one conclusion across many certificates, and invites
an omitted-permutation error.

The base colouring formula already chooses a canonical representative by ordering colour classes by
least element. That does not remove the issue: distance to a separately labelled reference witness
still depends on how the two palettes are aligned.

## Decision

`ColouringProblem::encode_with_witness_hamming_ball_up_to_palette_permutation` adds one existential
bijection from reference-witness colours to model colours. A `k` by `k` Boolean matrix has exactly
one true entry in every row and column. For each compared point and candidate model colour, a Tseitin
variable is equivalent to “the reference colour maps here AND the point has this model colour.” One
match variable is equivalent to the disjunction of those conjunctions. ADR-0583's generic
weighted-at-most encoder then bounds the number of negated match variables.

This is one complete CNF for distance minimized over all palette permutations. It remains complete
when the source formula uses canonical symmetry breaking: the source chooses one representative of
the candidate orbit, while the independent existential bijection aligns the reference witness to
that representative.

The result wrapper validates the full composed model before projecting exactly the original
colouring variables, and separately recovers the one-based palette bijection. Bijection/match
variables and clauses are checked against the caller's explicit weighted-construction ceilings;
arithmetic overflow and resource exhaustion decline through typed errors. The labelled API remains
available because it is smaller and is the intended fixed-coordinate local-search primitive.

## Evidence

An exhaustive two-colour, three-point control checks every candidate colouring at every radius
against explicit enumeration of both palette permutations. A second control starts from a literal
palette relabelling, obtains SAT at orbit radius zero, projects the canonical source colouring,
recovers mapping `[2,1,3]`, and replays the unrestricted source formula. A resource-ceiling control
fails closed. The earlier checked control continues to prove that the labelled API intentionally
rejects the same relabelled center at radius zero.

The 405-point Rado radius-22 orbit query is the first real consumer. Its deterministic formula has
14,194 variables / 327,843 clauses / 6,960,997 bytes, SHA-256
`33e5f3abed2a863aa4f09be3e518d2442f8d5b63d1478ef5eb7af2cf5403b2cc`. A mathematical conclusion
requires a terminal SAT model replay or a completed DRAT accepted by the independent checker; a
running proof prefix carries no credit.

## Alternatives

- Enumerate `k!` labelled formulas: rejected because completeness would move into an external loop
  and certificate set.
- Compare only canonicalized witness and model strings: rejected because a SAT encoding cannot
  assume that post-hoc normalization preserves a pre-normalization distance bound.
- Remove source symmetry breaking: sound but needlessly enlarges every family formula and changes
  canonical bytes that existing certificates pin.

## Consequences

Colouring repair neighborhoods can now be reported either in explicit label coordinates or as an
intrinsic palette-orbit distance, with distinct APIs and receipts. The orbit encoding adds
`k^2 + nk + n` definitional variables before weighted cardinality; it is expected to be harder than
the labelled query and must remain behind explicit resource limits.
