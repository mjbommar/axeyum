# ADR-0145: Stack-emitted not-AND CNF clauses

Status: accepted
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

The decision is accepted because exhaustive truth-table coverage includes
an internal both-direction not-AND gate with two private negated-AND factors,
the full CNF/SAT suites pass, and clean representative repetitions improve
end-to-end canonical time with identical clause/variable counts. A full-tier
confirmation passes the same semantic and performance gates.

## Evidence

All 283 `axeyum-cnf` unit tests pass, including an exhaustive 32-row truth table
for a both-direction not-AND gate whose two factors are private negated ANDs.
The complete crate integration tests, all 30 SAT-BV integration tests, and
strict Clippy also pass under the 4 GiB cap.

Against the accepted ADR-0144 revision, five clean representative canonical
processes improve:

- median total: 0.19380 → 0.18985 seconds (-2.04%); and
- median CNF encoding: 0.07813 → 0.07298 seconds (-6.60%).

The 13,462-query full confirmation is 100% decided with 1,774 SAT and 11,688
UNSAT results, zero errors, oracle/manifest disagreements, or model-replay
failures. It improves:

- total: 19.2172 → 18.6909 seconds (-2.74%);
- CNF encoding: 7.6588 → 7.2313 seconds (-5.58%);
- gate emission: 3.5579 → 3.1861 seconds (-10.45%); and
- Axeyum/Z3 ratio: 2.470x → 2.399x while Z3 is stable at 7.78/7.79 seconds.

Both revisions emit exactly 49,199,541 clauses with the same variable and gate
counts, including 2,232,632 not-AND gates. The accepted full artifact SHA-256
is `d2920cbf660564333d2b0b2bb7fcb5128f2d6c3416491b9ec220752417285a63`;
raw artifacts remain beside the access-controlled capture. The compact result
is recorded in `bench-results/glaurung-qfbv-2026-07-14.md`.

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

The emitter is more explicit but remains bounded to four small match arms. It
removes millions of short-lived heap allocations and clause clones on the
measured client families without changing CNF content. CNF remains the largest
stage, so the next GQ5 slice should inspect the remaining root-emission and
planning work rather than tune SAT.
