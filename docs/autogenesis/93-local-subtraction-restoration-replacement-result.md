# Local subtraction-restoration replacement result

Date: 2026-08-20

## Result

The V2 private joint quotient/remainder invariant reconstructs twice in fresh
Axeyum kernels with the same canonical declaration identity and an empty axiom
footprint:

```text
Axeyum.Autogenesis.divModGoReconstruct :
  forall y (hy : 0 < y) fuel x (hfuel : x < fuel),
    y * Nat.div.go y hy fuel x hfuel +
      Nat.modCore.go y hy fuel x hfuel = x
```

Both runs produce identity
`f8d6592cd39d5f249acf0f695b1d77bd255dc9f630e3a588a0044fe62d3360a4`.
The 230-declaration closure contains no axioms.

## Bottom-up repair

V1's sole assumption-bearing dependency, official `Nat.sub_add_cancel`, is
gone. V2 proves subtraction restoration locally by primitive recursion and
uses the separately bound statement `Nat.succ_sub_succ_eq_sub` only at the
opaque successor/successor subtraction step. Neither `Nat.sub_add_cancel` nor
`Nat.add_sub_of_le` appears in the direct dependency set.

This is the desired bottom-up shape: measure the exact contaminated edge,
replace only that edge, and recheck the whole theorem closure rather than
trusting source-level intent.

## Evidence and authority

The authored V2 source is
[`autogenesis_div_mod_go_reconstruct_v2.lean`](../../scripts/lean/autogenesis_div_mod_go_reconstruct_v2.lean).
It uses no proof search and V1 remains unchanged.

The proof-bearing stream remains model-inaccessible in a read-only external
pack whose manifest SHA-256 is
`e140c77f571b73a45bfe7260ca5a9ffc56555201538a3684e3783644fc2de777`.
Git retains identities, both import summaries, the exact direct dependency set,
and mutation-tested no-credit boundaries.

This result accepts one private support theorem. It grants no public
`Nat.div_add_mod` lift, balanced Bézout theorem, cancellation theorem,
Fibonacci target submission, receipt, fact transition, evaluation credit, or
ledger write.

## Next

Preregister the wrapper lift from the accepted fuel invariant through official
`Nat.div` and `Nat.mod`, including the zero-divisor branch. Require exact type
identity with official `Nat.div_add_mod`, then reconstruct it twice before
advancing to balanced Bézout.

## Verification

```sh
python3 scripts/check-autogenesis-euclidean-local-subtraction-replacement-result.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_euclidean_local_subtraction_replacement_result
```
