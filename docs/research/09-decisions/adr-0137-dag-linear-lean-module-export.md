# ADR-0137: DAG-linear Lean module export for corpus-scale proofs

Status: accepted
Date: 2026-07-13

## Context

ADR-0109 made repeated closed proof subterms shareable and ADR-0135 used that
exporter for genuine source-bound quantified-BV reconstruction.  The public
`psyco-107-bv` certificate still failed its Lean stress route: optimized runs
under a 4 GiB address-space cap reached roughly 3.45 GiB RSS, then requested one
2 GiB allocation and aborted.  The checked kernel proof itself completed; the
failure began in self-contained Lean-module export.

Three serializer boundaries caused the gap:

1. declaration reachability walked the hash-consed expression graph as a tree,
   revisiting shared subgraphs exponentially;
2. ADR-0109 retained at most 16,384 repeated nodes and did not cut long
   single-use closed resolution chains; and
3. declaration types and values were rendered before the top-level proof-share
   plan, so a large source-assertion axiom could still expand as a tree.

This closes ADR-0135's corpus-scale proof-sharing follow-up.  It does not change
the reconstructed theorem, kernel checker, admitted source shape, or trusted
axioms.

## Decision

**Export compact Lean modules in time and space proportional to the reachable
closed expression DAG, using exact visited-expression reachability and
deterministic closed serialization chunks in both declarations and the final
theorem.**

- Declaration dependency discovery visits each `ExprId` once per root.  A
  constant dependency is a set-membership question; multiplicity is irrelevant.
- Every qualifying repeated closed compound expression may be shared; there is
  no count ceiling that silently reverts the residual proof to tree expansion.
- A large single-use closed region is cut after 512 unshared expression nodes.
  Selected descendants count as one reference, so a long resolution tail becomes
  a deterministic sequence of bounded definitions rather than one giant term.
- Final goal/proof chunks remain top-level definitions.  Declaration types and
  values use scoped `let` aliases because they must appear at their declaration
  point in dependency order.
- Only expressions with no loose de Bruijn variables and no free variables are
  shareable.  Generated alias names reserve environment and source-binder names,
  preventing capture.  Aliases are transparent definitional equalities and add
  no axiom or proof rule.
- The public corpus route remains an ignored, release-only scheduled stress gate,
  reproducible with `just test-quant-bv-lean-stress`; ordinary workspace tests do
  not absorb a roughly 100-second proof export.

## Evidence

Before this decision, the exact release stress test aborted after about 130
seconds wall time at 3,454,552 KiB maximum RSS with a failed 2 GiB allocation.
After DAG-linear dependency discovery and compact declaration/final-term export,
a timed one-pass routed test completes in 102.19 seconds at 2,697,384 KiB
maximum RSS under a 3 GiB test-process limit.  The final reproducible recipe
rerun completes in 106.51 seconds; its 4 GiB envelope also accommodates a cold
optimized Rust build.

The focused serializer suite covers:

- a 20-level exponentially shared dependency DAG, whose constant dependency is
  visited once;
- more than 16,384 qualifying repeated closed nodes, proving there is no hidden
  fallback ceiling;
- a 20,000-node single-use chain, proving deterministic chunk insertion;
- compact local chunks inside a large axiom type;
- rejection of open binder-dependent shares and avoidance of source-binder name
  capture; and
- deterministic legacy and compact rendering on the existing small theorem.

The refreshed committed quantified-BV baseline is 54/54 decided (36 SAT, 18
UNSAT), 100% decided, `DISAGREE=0`, with zero errors and replay failures.  The
exact audit is evidence-certified/rechecked 54/54, marks 45/54 dominant, and now
kernel-reconstructs 9/18 UNSAT rows to Lean, with zero audit errors or timeouts.
`psyco-107-bv` is the added Lean row.

## Alternatives

- **Raise the process memory limit.** Rejected: it preserves exponential
  traversal and makes proof export depend on host RAM.
- **Only remove the 16,384-share cap.** Rejected by measurement: the real target
  still made the identical 2 GiB allocation because dependency reachability and
  declaration rendering occurred outside that plan.
- **Axiomize the residual or its ground instances.** Rejected: it would erase
  ADR-0135's genuine source-instantiation theorem boundary.
- **Hoist open expressions.** Rejected: a top-level definition cannot capture a
  local binder; doing so would change the term or produce invalid Lean.
- **Put the corpus target in the default debug suite.** Rejected: the proof is a
  scheduled resource gate, not a suitable per-edit unit test.

## Consequences

Corpus-scale checked proofs can retain kernel DAG sharing through complete Lean
module export, including source declaration types.  The quantified-BV audit now
credits `psyco-107-bv`, raising Lean UNSAT coverage from 8/18 to 9/18 and exact
dominance from 44/54 to 45/54.  Export remains expensive and peaks near 2.7 GiB;
future work should reduce proof construction and rendered-module size rather
than weakening the 4 GiB scheduled gate.  The next P2.6 proof lane ranks the
remaining ADR-0124/0126/0127/0128/0129/0130/0131/0132/0133 quantified-BV
families for source-bound Lean reconstruction.
