# Source-bound semantic function-contract receipt

Date: 2026-08-19

## Result

Commit `dc1a0e1a5` turns ADR-0488's synthetic function-contract control into a
durable two-kernel receipt. The receipt is issued only after independently
recomputing the proof-isolated generic theorem, the exact source definition,
the source-specialization witness, and the concrete specialized theorem.

The checked chain is now:

```text
proof kernel                           source kernel
------------                           -------------
forall f, contract f -> goal f         exact transparent definition d
proof uses only local contract         witness : contract d
         |                                      |
         +---------- identical mirror ----------+
                                                |
                                  generic-proof d witness
                                                |
                                                v
                                      exact concrete theorem
```

The concrete proof value must be literally the generic theorem applied to the
exact source constant and exact witness. Merely proving an equivalent result by
another route is not enough to issue this receipt: the receipt certifies this
particular decomposition and trust boundary.

## What is bound

The versioned canonical payload records:

- source name, declaration content, function type, and binder position;
- the exact-source-specialized local contract and its binder position;
- generic theorem declaration, type, proof, and complete transitive dependency
  closure from the proof-isolated kernel;
- source witness declaration, proof, and complete dependency closure including
  the exact source definition;
- the specialized goal;
- concrete theorem declaration, proof, complete dependency closure, axiom
  footprint, and theorem dependencies; and
- a digest over every preceding field.

Verification does not trust those fields. It reissues the receipt from both
live kernels and compares the complete canonical object. Version 1 requires a
monomorphic transparent source definition, a generic proof with no theorem or
axiom dependency, a witness with no theorem or axiom dependency, an axiom-free
concrete result, and exactly the generic theorem plus witness as the concrete
theorem dependencies.

## Controls

The executable controls reject:

1. a same-typed but differently defined source function;
2. a different theorem substituted as the source-kernel generic mirror;
3. a concrete theorem proved directly instead of by the certified application;
4. mutated source identity;
5. mutated specialized contract identity;
6. moved contract binder position;
7. mutated witness proof identity; and
8. a circular witness supplied by an upstream answer axiom.

The last control matters: the kernel correctly accepts the axiom-backed term as
typed, while the receipt correctly refuses it as independent evidence. Type
checking and assurance remain distinct gates.

## Scope and next turn

This closes a reusable receipt mechanism, not a Mathlib result, proof-producer
operation, or ledger admission. No held-out row or upstream proof body was
inspected.

The next turn should preregister one real pointwise-function identity and one
train/development statement whose proof actually demands a small definition
equation. Selection must combine the bottom-up census (exact identity, body
shape, footprint) with top-down target demand (which observation is required by
the goal). It must freeze the contract derivation rule and budgets before
running the producer. Smallest implementation body alone is not a selection
rule.

## Reproduction

```sh
cargo test -p axeyum-lean-import --test semantic_function_contract
cargo clippy -p axeyum-lean-import --all-targets --all-features -- -D warnings
```
