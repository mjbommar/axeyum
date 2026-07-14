# ADR-0153: Fold constants across associative bit-vector additions

Status: proposed
Date: 2026-07-14

## Context

The repeated full Glaurung baseline makes the next cold-path target
family-specific rather than stage-generic. In canonical run 003, the
`slice-partial` family is 1,584/13,462 queries (11.8%) but consumes 6.207/15.627
seconds (39.7%) and runs 3.82x slower than in-process Z3. It creates 16.91
million AIG nodes and emits 22.87 million clauses. Bit blast plus CNF encoding
consume 4.379 seconds, 70.6% of that family's Axeyum time.

A source-shape audit explains the concentration. The manifest-selected
`slice-partial` scripts contain 377,320 lexical `bvadd` occurrences but only
11,417 `bvsub` occurrences. Large instances repeatedly add one symbol and many
machine constants before comparing or Booleanizing the result. The current
canonicalizer flattens and sorts associative-commutative `bvadd` trees, but when
the flattened list has more than two operands it rebuilds the tree immediately.
The binary constant folder therefore never combines constant leaves separated
by a symbolic leaf, and each surviving constant produces another wide ripple
adder downstream.

The evidence artifact is canonical full run 003 at revision `0cfd6cdc`, SHA-256
`32ceead9d38095e7fc54f3bb430b103cdb67c80c4a3362420f61b46e28b0fb8f`.
The lexical operator inventory is diagnostic source evidence, not a claim that
all occurrences survive canonicalization. Candidate rule counts and downstream
AIG/CNF changes must establish the actual opportunity.

This is the next bounded GQ2/GQ3 experiment. It does not authorize a general
algebraic normalizer, non-commutative subtraction reassociation, or an AIG/SAT
change.

## Decision

Add exact rule `bv.add_constant_chain.v1`, subject to the Glaurung acceptance
benchmark.

- During existing associative-commutative `bvadd` flattening, sum all constant
  leaves modulo `2^width` and replace them with at most one constant leaf.
- If the modular sum is zero and symbolic leaves remain, omit the constant.
  If only constants remain, return their folded constant.
- Support both the scalar and arbitrary-width bit-vector constant
  representations; the rule must not introduce a 128-bit semantic ceiling.
- Sort the resulting leaf list by `TermId` and rebuild through the existing
  deterministic balanced-tree path. Do not duplicate symbolic leaves or change
  their multiplicity.
- Record this transformation under its own stable rule ID, not under
  `commutative.operand_order.v1`, so artifacts can attribute its exact use.
- Keep the work linear in the already-flattened operand list and create at most
  one constant plus the existing balanced replacement tree. Identity model
  projection and untouched-original replay remain the soundness boundary.
- Advance the benchmark rule-set identity to `axeyum-rewrite-default-v3`; v2
  and v3 artifacts must not be compared as the same configuration.

Before corpus timing, require manifest coverage, focused structural tests,
exhaustive small-width evaluator equivalence, arbitrary-width coverage, Z3
differential SAT/UNSAT checks, formatting, and strict Clippy under the 4 GiB
cap. Then run five clean representative processes. Continue to the guarded
five-process full comparison only if the new rule fires on the target family,
reduces its post-word/AIG/CNF work, preserves 100% decisions and all replay
gates, and improves representative end-to-end timing beyond observed noise.
Accept only if the full comparison preserves every validity gate, materially
improves `slice-partial`, and passes the existing 3% ratio / 3% Axeyum-total /
2% absolute-Z3-drift alarms. Otherwise restore v2 and defer this ADR.

## Evidence

The full-run family attribution is:

| Family | Queries | Axeyum | Share | Z3 | Ratio | Bit blast | CNF | New AIG nodes | Clauses |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `register-slice` | 11,606 | 9.267 s | 59.3% | 5.862 s | 1.58x | 2.807 s | 2.880 s | 22,744,762 | 25,829,051 |
| `slice-partial` | 1,584 | 6.207 s | 39.7% | 1.626 s | 3.82x | 2.105 s | 2.274 s | 16,911,901 | 22,872,958 |
| `arithmetic` | 251 | 0.152 s | 1.0% | 0.202 s | 0.75x | 0.047 s | 0.052 s | 403,662 | 496,373 |

`slice-partial` creates about 10,677 new AIG nodes per query versus about 1,960
for `register-slice`, despite having far fewer queries. Existing rewrite
telemetry reports 178,325 commutative-order applications in `slice-partial` but
only 46,402 BV constant folds, consistent with flattened mixed
symbol/constant chains surviving the binary-only fold boundary. The candidate
benchmark will replace that inference with direct rule and construction counts.

## Alternatives

- **Normalize `bvsub` into addition plus negation in the same change.** Deferred:
  subtraction is non-commutative, is 33x less frequent in the target source
  inventory, and would confound the narrow add-chain attribution.
- **Recognize affine additions directly in the AIG or CNF encoder.** Deferred:
  exact word reduction avoids constructing the redundant circuit at all and is
  independently testable before changing lowering or proof mappings.
- **Tune SAT for the family.** Rejected at this point: bit blast and CNF own
  70.6% of target-family time, while the source audit identifies removable
  construction.
- **Start broad relevant-bit lowering.** Deferred: the complete full-tier
  diagnostic demands 98.16% of post-word term bits; the targeted family rule
  has a more direct measured hypothesis.

## Consequences

Mixed symbolic/constant `bvadd` chains can collapse before bit blasting while
preserving exact modular semantics and model identity. The default rewrite
identity changes, and the extra flatten-list scan is paid by every canonical
`bvadd`; the real-corpus gate must therefore prove a net cold win rather than
assuming one.

Regardless of this experiment's result, Glaurung's next functionality-enabling
artifact remains an ordered worker/path/scope trace. The deduplicated cold pack
cannot validate warm push/pop reuse, delta preprocessing, cache frequency, or
model-choice effects.
