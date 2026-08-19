# Factorial-zero family admission

Date: 2026-08-19

Registration prestate: `22e49b92d9e4eac977cd232670898f3ad4f46d3b`

## Result

The flywheel reused one proof-free adapter family and one bounded proof grammar
to establish a second frozen Mathlib train fact. The machine frontier selected
`F:ml430-nat-descfactorial-zero-966b01df`; the exact registered operation
constructed and independently checked

```lean
∀ (n : ℕ), n.descFactorial 0 = 1
```

without a Mathlib proof value, axiom, prior theorem dependency, or dependency on
the target proposition definition. The ordinary typed transaction moved the
fact from `open` to `proved` and the settled-fact checker reconstructs the same
four-node reflexivity proof from the immutable stream.

This is reuse, not mere replay: `Nat.ascFactorial_zero` and
`Nat.descFactorial_zero` have different imported declaration closures, goals,
proofs, and exact authoritative operations. They share a proof-free source
family and producer/checker grammar.

## Durable chain

| Object | Content identity |
|---|---|
| Frontier before | `c86ae1d51b09ac8de45a45c29b11b732b20b72f4ce8f393784dc1c9ed955cbed` |
| Operation execution | `3675df4623f421cfc4c92df7a3c4523c1f915f1e7d5830621cb96662d2b05d0b` |
| Prepared transaction | `95675ccb8d5509a06efebd892382514c90932ef1947dccaa5e8b4454b46e36d5` |
| Durable admission event | `4cadf6dc6809a256743d58ad5c97dc6a8ef51c38d7736c5ac1146e93743fa8b8` |
| Frontier after | `32f1f2b00a50ab29dfede5c99807b0d24fc11bc74436181ed25a9b621d3fddf8` |
| Readiness delta | `0fa8dfa95754293d6d099baf37fe391e6d19488cbc04b5be9400071332f19939` |

The admission archive is read-only at
`/nas3/data/axeyum/autogenesis/admissions/22e49b92d-mathlib-nat-descfactorial-zero-v1/`.
Its exhaustive file index also covers a complete Git bundle and both retained
journal layouts.

## Crash and replay controls

The first apply attempt refused before intent because the journal and fact were
on different filesystems. The actual fault experiment used a journal beside the
`/tmp` fact checkout: it stopped after durable intent with exit status 75 and
left the fact byte-identical, then recovered solely from the transaction and
journal. The canonical journal was copied into the external archive; the
redundant first copy remains indexed as operational history.

The initial clean replay could not materialize this repository's 436 GB tracked
worktree on a 13 GB `/tmp` remainder. The replay tool now accepts a validated
scratch root. Commit `ddeec1fdd` reproduced the complete episode on `/data0` in
a detached worktree without reusing receipts. Its fresh execution, transaction,
event, and readiness identities are
`6ef789207ce41078dcf070e4eb267c8e0e9d956e7fb7a274f592cab07ce5c7d1`,
`37de48c03048b607c1c034153986e92b05dda1ddc9b6d41c25606da286906758`,
`8fa2e8b09b53248aefc2a5d0ebc76cc1bbd22cd3a17b9e6d2ac1498c371be151`,
and `b90274e57059a27066379c735028fd0fe744edf0229e5870e6a08e5bbec7a925`.
The replay digest is
`17c7de26fda0595fe636db5770db300d3b282a392b95550c37bdfcd904fd6311`.

## What changed—and what did not

The live frozen census now has two established rows, zero dispatchable rows,
and 136 pre-execution declines. The admission performed one authoritative write
and zero fixture writes. The fact is a dependency leaf, so `newly_ready` is
honestly empty; this turn demonstrates reusable acquisition but does not itself
increase dependency reach.

The next leverage point is not another exact reflexivity registration. A
proof-free type slice must move some of the 114 adapter rejections into isolated
producer reach while retaining transparent computation and rejecting every
proposition-valued assumption. After that boundary is frozen, the seven kernel
rejections and fifteen producer declines become the next search curriculum.

## Reproduction

```sh
python3 scripts/check-autogenesis-statement-reflexivity-admission.py \
  --manifest artifacts/autogenesis/mathlib-factorial-zero-admission-v1.json
python3 scripts/check-autogenesis-factorial-zero-family.py
python3 scripts/check-autogenesis-fact-operation.py \
  --fact artifacts/facts/F-ml430-nat-descfactorial-zero-966b01df.json
```
