# ADR-0145: Stack-emitted not-AND CNF clauses

Status: proposed
Date: 2026-07-14

## Context

ADR-0144 reduced full canonical Glaurung CNF time from 9.40 to 7.66 seconds
without changing CNF content. Gate and root emission still cost 3.56 and 1.40
seconds. The recognized not-AND family accounts for 2,232,632 gates on that
tier, including 1,516,100 in `slice-partial` and 692,811 in `register-slice`.

The current not-AND emitter allocates a temporary `Vec` for every forward
factor. For reverse implication it constructs `Vec<Vec<EncodedLit>>`, cloning
partial clauses while expanding the Cartesian product of two factors, and then
copies each temporary again through the ordinary normalizer. This temporary
ownership is unnecessary: a `NotAndGate` has exactly two factors, each either
one literal or one private negated AND, so every emitted clause has at most
three encoded literals and at most four reverse clauses exist.

This is the next bounded GQ5 allocation slice identified by artifact v27 after
[ADR-0144](adr-0144-collision-safe-cnf-clause-dedup-index.md).

## Decision

Emit not-AND forward and reverse clauses directly from fixed stack arrays,
subject to the Glaurung acceptance benchmark.

- Forward implication emits one two-literal clause for a literal factor or one
  three-literal clause for a private negated-AND factor.
- Reverse implication matches the four exact two-factor shapes and emits one,
  two, or four three-literal clauses in the same left-to-right Cartesian order
  as the former expansion.
- All clauses still pass through the same constant/tautology/literal-duplicate,
  sort, fingerprint, and exact-clause-duplicate checks. Formula ownership,
  variable allocation, clause order/content, lift maps, and replay do not
  change.
- The general `CnfClause` representation and public API remain unchanged. This
  optimization removes only encoder-local temporary allocations.

The decision becomes accepted only if exhaustive truth-table coverage includes
an internal both-direction not-AND gate with two private negated-AND factors,
the full CNF/SAT suites pass, and clean representative repetitions improve
end-to-end canonical time with identical clause/variable counts. A full-tier
confirmation is then required; otherwise the ADR is deferred and the simple
temporary-vector implementation is restored.

## Evidence

Pending implementation measurement. The motivating artifact is recorded in
`bench-results/glaurung-qfbv-2026-07-14.md`.

## Alternatives

- **Change `CnfClause` to inline storage.** Deferred: that alters a public,
  checker-wide representation and adds dependency/surface cost before measuring
  the localized 2.23-million-gate allocation site.
- **Skip the common normalizer for recognized gates.** Rejected: direct roots
  can substitute Boolean constants, and retaining one exact normalization and
  dedup boundary is simpler and safer.
- **Change the not-AND encoding clauses.** Rejected: this experiment isolates
  allocation behavior and must keep byte-identical CNF.

## Consequences

The emitter becomes more explicit but remains bounded to four small match arms.
It should remove millions of short-lived heap allocations and clause clones on
the measured client families. The real-corpus benchmark decides whether branch
and code-size cost outweighs that saving.
