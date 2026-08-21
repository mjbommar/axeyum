# Exact Fibonacci coprimality admission

Date: 2026-08-20

Registration prestate: `b1f9cdd60624dfb504d5a3b1b958994c7892d1f6`

## Result

The flywheel converted the dependency-bound semantic receipt for exact official
Lean 4.30 `Nat.fib_coprime_fib_succ` into durable ledger knowledge. The machine
frontier selected exactly
`F:ml430-nat-fib-coprime-fib-succ-162fc738`; no caller supplied its theorem,
premise set, route, checker, footprint, status, or evidence row.

The registered operation retained all eight direct theorem names and canonical
declaration identities, the 115-row transitive replay digest, the exact source,
candidate, goal, proof, and declaration identities, and an empty complete axiom
footprint. This is a compositional theorem admission, not an isolated-proof
claim.

## Durable chain

| Object | Content identity |
|---|---|
| Frontier before | `3eef4c977f9990b3204153a42ba31c1b892d5b22cab3e8d6c47e45cc8da71658` |
| Operation execution | `1dc593170da515d02cc871853f62701a50025e824bd138a8267df10f20758e2b` |
| Prepared transaction | `f44abc6f2e22c3e354f4a2529f7ff064902b7457464a843e449d3cbfdd749849` |
| Durable admission event | `9b925a433c03e2cb61b3334d3805c7721fddf903fdac3fbaad9a73c1530d9582` |
| Frontier after | `1aa08dd6f80a8578870bb0b7fdc9b054163d22398b09c54a62f6eb253e37ff86` |
| Readiness delta | `95eba953aebbc2935b5a4021fd122b54cf1b0873d8609e7a9c98acb9833ae21c` |

The complete read-only archive, including the durable journal and a complete
Git bundle of the registration prestate, is
`/nas3/data/axeyum/autogenesis/admissions/b1f9cdd60-mathlib-nat-fib-coprime-v1/`.

## Crash control and measured unlock

The first apply stopped after durable intent with exit status 75. The fact was
byte-identical to its prestate. Recovery using only the prepared transaction
and same-filesystem journal then produced exactly one durable event and one
authoritative ledger write. All 341 facts validate, and the settled operation
checker independently replays the exact dependency-bound receipt.

The event made exactly one descendant newly ready:

- `F:ml430-nat-gcd-fib-add-self-5a92d5e3`

This readiness result is derived from the fact DAG after the durable event. It
is not inferred from theorem names or claimed by the receipt issuer.

## Clean replay

Commit `3f96b54635c03c23258600ebc7129d5496d8a0da` reproduced the complete
episode in a detached clean worktree. The replay reconstructed the historical
open fact at the registration prestate, created fresh execution and transaction
receipts, injected the same intent fault, recovered, rechecked the settled fact,
and reproduced the same newly ready child without reusing the retained episode.

The fresh execution, transaction, event, and readiness identities are
`b8d2ee44f3b3d15bf1fb3d0ccd51001f4bda4847ee122b7306cdf394226ebccd`,
`a0513b5190208dc4b4e3f9d07e6b2adc476c6df87871f5d5878832fd801f6686`,
`0a392e8077dbd34331bc441399bbd4db6cb940e96170d08f43efe44cc0cb5bdf`,
and `a5b758977c7ac5823cf3b1d5a61c5371990aa8de1c570cfc841418d070751855`.
The clean replay semantic digest is
`fd83e8431c506bedea825f7a9a857190b26ad4e54be0faa9066166aa99845983`.

The read-only replay archive is
`/nas3/data/axeyum/autogenesis/replays/3f96b5463-nat-fib-coprime-v1/`.

## Reproduction

```sh
python3 scripts/check-autogenesis-statement-reflexivity-admission.py \
  --manifest artifacts/autogenesis/mathlib-nat-fib-coprime-admission-v1.json
python3 scripts/check-autogenesis-fact-operation.py \
  --fact artifacts/facts/F-ml430-nat-fib-coprime-fib-succ-162fc738.json
```

No held-out outcome was inspected and no evaluation credit was granted. The
next turn starts from the measured child unlock: qualify
`Nat.gcd_fib_add_self`, then preregister its smallest honest proof plan before
any target submission.
