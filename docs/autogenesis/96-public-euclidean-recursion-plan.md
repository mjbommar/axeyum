# Public Euclidean recursion plan

Date: 2026-08-21

## Decision

The successor does not retry the failed transparent-wrapper lift. It proves the
public equation directly by synchronizing the proof-free public recursion
statements `Nat.div_eq` and `Nat.mod_eq`.

For the recursive branch, the dividend decreases from `m` to `m - n` under
`0 < n` and `n <= m`; `Nat.sub_lt` supplies the registered well-founded
decrease. The algebra is the same as the accepted private invariant, including
a local primitive-recursive subtraction-restoration proof. The false equation
branch closes with local multiplication/addition zero proofs.

## Exact target

The one authored theorem must have Lean expression representation identical to
the immutable `Nat.div_add_mod` statement, reconstruct twice with the same
canonical identity, and have an empty kernel-derived footprint. The second run
is forbidden unless the first passes all gates.

Exactly twelve proof-free statements are bound. The official target proof, the
failed wrapper route, the private `div.go` theorem as a dependency, added
statement names, proof search, and upstream proof bodies are forbidden.

## Authority

One source path, one public support declaration, and two kernel submissions are
permitted. No balanced-Bézout, cancellation, Fibonacci target, executor, fact,
evaluation, or ledger authority follows from this plan.

## Verification

```sh
python3 scripts/gen-autogenesis-euclidean-public-recursion-plan.py --check
python3 -m unittest \
  scripts.tests.test_gen_autogenesis_euclidean_public_recursion_plan
```
