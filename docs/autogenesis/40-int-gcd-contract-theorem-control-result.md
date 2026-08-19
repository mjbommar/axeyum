# First contract-backed semantic theorem receipt

Date: 2026-08-19

## Result

The preregistered `Int.gcd_def` bridge ran exactly once and succeeded. The
independent kernel admitted:

```text
forall i j : Int,
  Int.gcd i j = Nat.gcd (Int.natAbs i) (Int.natAbs j)
```

The producer introduced exactly two binders, constructed five nodes, used no
retry, and issued semantic theorem receipt
`2aaf51c928c786b8a72b635d8fb783b4dc1bbdde5ab9b7c18c8e79ca0213f9d7`.
Its theorem axiom footprint is empty. The sealed observation has semantic
identity `2bbbaeb67c44fb27520873fbda3667335263c1887d6caf926f4f550a507765cb`
and file identity
`2be77236d3f8d05edb989340768fb4203233da19a040e07da0a5a4d31821ae16`.

This is mechanism evidence, not evaluation yield. It wrote no fact-ledger row
and receives zero evaluation credit.

## What the receipt proves

The new receipt performs four checks as one replayable boundary:

1. reissue and compare the exact trace-backed `Int.gcd` source-contract
   receipt;
2. reconstruct its exact pointwise source equation;
3. construct only the frozen `trace-contract-reflexivity-v1` proof and admit it
   through the independent kernel; and
4. bind theorem type, proof, declaration identity, axiom footprint, operation,
   and budget in a second content-addressed receipt.

Mutation controls reject a changed source receipt, changed theorem receipt,
axiom footprint, second invocation, evaluation credit, or promotion of
diagnostic dependencies to authority.

## The 52-theorem distinction

The admitted theorem has zero direct theorem dependencies and zero axioms. Its
complete declaration closure nevertheless contains 52 theorem declarations
below the transparent source implementation. That inventory is recorded in the
receipt as diagnostic metadata. It is not a whitelist and none of those
theorems becomes a producer premise.

The authority is instead the separately replayed structural source-contract
receipt: it checked the exact `Int.gcd` delta step while leaving `Nat.gcd`
opaque. This distinction prevents the old theorem-closure shortcut from
returning through the theorem receipt.

## Over the horizon

The infrastructure seam is no longer the reason to avoid a real target.
`Int.gcd_fib` remains the first compounding evaluation horizon, with two open
direct premises:

```text
Int.fib_neg ─┐
             ├─> Int.gcd_fib
Nat.fib_gcd ─┘
```

The next turn should rank and preregister one of those premise facts under a
separate search budget. Establishing it would be mathematical progress;
repeating another defining-equation control would not.

## Reproduction

```sh
cargo test -p axeyum-lean-import --test trace_contract_theorem_receipt
python3 -m unittest scripts.tests.test_check_autogenesis_int_gcd_contract_theorem_control
python3 scripts/check-autogenesis-int-gcd-contract-theorem-control.py
```
