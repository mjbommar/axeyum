# ADR-0488: Semantic abstractions are discharged local contracts

Status: accepted
Date: 2026-08-19
Index-summary: Key definition contracts by exact source identity, expose them only as local generalized-goal binders, and require source-kernel specialization witnesses before concrete fact credit

## Context

The first complete producer census separates 24 exact slices from 114 slices
with 152 non-`Prop` definition abstractions. Generalization preserves and exactly
specializes the proposition's type, but a bare function parameter deliberately
forgets the source definition's behavior. Proof search over those 114 goals is
therefore not yet a fair measure of producer capability.

The kernel-backed semantic census finds 30 rendered names but 32 exact
definition identities: `Int.gcd` and `Nat.gcd` each have two distinct source
content identities across export contexts. It also derives three contract
shapes from checked declaration types: five predicate identities covering 73
bindings, fifteen pointwise-function identities covering 50 bindings, and
twelve nullary structure or instance identities covering 29 bindings.

## Decision

A semantic abstraction contract is keyed by the complete source identity:
rendered name, source content digest, instantiated type digest, and universe
instance digests. Rendered names are diagnostic labels and never cache keys.

Contracts enter a generalized proposition only as local Pi-bound premises.
They are not installed as environment axioms. Before any proof of that
proposition receives credit for the concrete source fact, an independent
source kernel must construct and check a specialization witness establishing
each premise for the exact source definition. The durable receipt binds the
contract proposition, exact source identity, witness identity, and complete
axiom and theorem footprint.

Version 1 contract proposals may be derived only from transparent definition
behavior, previously ordered abstractions, and retained proof-free terms. They
may not inspect the target proof, target outcome, or held-out rows, and may not
rest merely on a proposition equivalent to the target. The supported design
shapes are:

1. predicate equivalence between the abstract predicate and its transparent
   source body;
2. pointwise equality between an abstract function and its transparent source
   body; and
3. only the observational projections actually required from a nullary
   structure or instance, never whole-structure equality or proof-field
   equality by default.

Concrete fact credit remains unavailable unless every specialization witness
is axiom-free, or every remaining premise dependency is independently
established and explicitly bound under the ordinary Axeyum evidence policy.
Transitive implementation-closure inventories are diagnostics, not an
automatically authorized premise set.

## Evidence

- The exact-commit census reproduces 152 bindings across 114 unsealed rows,
  with no held-out access, contract generation, or ledger writes.
- Name-only identity is empirically insufficient: 30 names represent 32 exact
  source identities.
- Twenty-nine of 32 definitions have no direct theorem dependency even though
  the transitive closure contains 6,346 theorem-name occurrences. Most
  contamination is therefore indirect implementation closure, not a justified
  list of mathematical premises.
- The existing exact specialization replay already proves that generalized
  propositions return definitionally to their frozen source goals.

## Alternatives

- **Retain source definitions in every proof-search kernel.** Rejected because
  their implementation closure reintroduces upstream theorem values and makes
  proof isolation illusory.
- **Install semantic equations as axioms.** Rejected because it moves the
  missing proof into the trusted base and makes axiom-free output impossible.
- **Key contracts by rendered name.** Rejected by the observed `Int.gcd` and
  `Nat.gcd` identity variants.
- **Use full structure equality for nullary instances.** Rejected because
  proof fields and irrelevant projections inflate obligations beyond the
  observations needed by the target.

## Consequences

The first implementation should prototype one small pointwise function
equation with mismatched-contract and circularity controls. In parallel, proof
planning may proceed on the 24 exact slices. Predicate contracts follow after
the function control; observational projection synthesis remains a separate,
more delicate increment. No census row or fact status changes through this
decision alone.
