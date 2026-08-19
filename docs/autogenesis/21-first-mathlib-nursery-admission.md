# First authoritative Mathlib nursery admission

Date: 2026-08-18

Implementation prestate: `e70ab2449bdaf165c771f559917014d9d3fac739`

## Result

The flywheel has established its first ordinary fact from the frozen Mathlib
nursery. `F:ml430-nat-ascfactorial-zero-fd183202` moved from `open` to `proved`
only after the machine frontier selected its exact registered operation, a
fresh import reconstructed and independently checked the proof, and the
crash-safe fact transaction emitted its durable admission event.

This is not imported-Mathlib proof credit. The upstream theorem body was never
present in the proposer or checker environment. The constructed term is the
four-node generic reflexivity proof recorded before operation registration.

## Durable chain

| Object | Content identity |
|---|---|
| Frontier before | `78cb1b70a4e93b86e59ee7689724644d654dd565e1227061faf3f7edf4e78566` |
| Operation execution | `9846be9e23ca38790303783b464ffa25fd3cfe8396e064b299bd90c940d1d391` |
| Prepared transaction | `00cb1baf44bc8f5f6b1e9b8560dd2ffab0b4559bfee108907e56676765b8e0cc` |
| Durable admission event | `37f55c3f662d473dc0c562ecfd4a1726387ed6cf325a1e725910bd0b061c4cc4` |
| Frontier after | `52a0d19a195225b2daf68e4db396530544f94f9f40b162e1fc2f5648d6dc4d43` |
| Readiness delta | `6f960c02e16aa43f50b923f8c240a4ae4779a5b57b31690b40fd7af2c2b45597` |

The complete append-only bundle is retained at
`/nas3/data/axeyum/autogenesis/admissions/e70ab2449-mathlib-nat-ascfactorial-zero-v1/`.
It includes the transaction journal and a 319,582,959-byte Git bundle whose
verification reports complete history.

## Failure and assurance controls

- Fault injection stopped immediately after durable intent with exit status
  75; the fact remained byte-identical to the open prestate.
- Recovery used only the prepared transaction and journal, then atomically
  wrote the after-fact and durable event.
- The settled-fact checker reimported the immutable external stream and rebuilt
  the exact proof in a fresh arena.
- The result has zero axiom, prior-theorem, and target-definition dependencies.
- The readiness delta derives one authoritative ledger write, zero fixture
  writes, removal of the admitted fact from the queue, and no newly ready fact.
- The frozen nursery census now distinguishes 1 already-established row from
  137 pre-execution declines and reports zero redispatchable rows.

## Independent clean replay

Commit `b9daf91a5473ae7e33e33ed8853262575d8cb0a2` was checked out into a clean,
detached worktree. The replay reconstructed the open fact from the registered
implementation prestate, recomputed the frontier, re-executed the operation,
repeated the intent fault and recovery, rechecked the settled fact, and
recomputed the readiness delta without reusing the retained receipts.

The fresh execution, transaction, durable event, and readiness identities are
`07125ab62dcd65056597fdff8a92c3ba2b66edba2c6d5b87dc8b212549139d8f`,
`cc416eae1558719b9b6b7b1e8ec5c91516b988223ed2c5e9560a8933e57b390d`,
`7029c1e195cc3b6cf1fd97798aec0a455ecd60bbd3efde088c89c39accb2c8ca`,
and `87c7731c4dc0bfa574737fa65faf987f8a3cb9019fef5ab54f0b49b85686f68f`.
Their content-addressed replay report is
`265571de5fadd6e4b7ce505ea38ac0c140e6685748e6cac322e825f775c7b27b`.
The read-only external replay directory is
`/nas3/data/axeyum/autogenesis/replays/b9daf91a5-mathlib-reflexivity-v1/`.

## Scope and next horizon

This closes one complete **library-source -> checked goal -> constructed proof
-> registered execution -> durable fact** turn. It does not yet demonstrate
generalization: the operation is exact to one train row, the proof family is
definitional reflexivity, and the fact is a dependency leaf.

The immediate next step is to work bottom-up by measuring which remaining
train/development statements fit the existing reflexivity grammar, and
top-down by adapting one
non-reflexive statement family whose proof requires a newly produced library
fact. Held-out rows remain inaccessible until the preregistered evaluation
boundary.

## Reproduction

```sh
python3 scripts/check-autogenesis-statement-reflexivity-admission.py
python3 scripts/check-autogenesis-fact-operation.py \
  --fact artifacts/facts/F-ml430-nat-ascfactorial-zero-fd183202.json
python3 scripts/create-autogenesis-nursery-dispatch-baseline.py --check
```
