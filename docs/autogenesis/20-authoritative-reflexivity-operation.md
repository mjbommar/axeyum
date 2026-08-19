# Authoritative statement-reflexivity operation

Date: 2026-08-18

## Result

The first frozen Mathlib train row now has exactly one authoritative operation:
`authoritative-mathlib-statement-reflexivity-v1`. The machine frontier can
select it, but registration itself does not execute the producer or change the
ledger.

The fourth authoritative driver binds all of the following before execution:

- the exact fact ID and `lean4-surface` statement digest;
- the immutable statement-adapter and checked-candidate manifests;
- the external NDJSON artifact digest, size, record count, and read-only mode;
- the target definition, goal, proof, and target-declaration digests;
- fixed budgets of eight Pi binders and sixteen constructed nodes; and
- the empty axiom, theorem-dependency, and target-dependency result.

The source export remains on the shared content-addressed artifact store. It is
not copied into Git. An unavailable or changed external object is an
authoritative execution failure, not a skipped or successful check.

## Trust path

The producer remains syntactic and untrusted. Each execution starts from the
proof-free export, creates a fresh importer/kernel arena, proposes the bounded
`Eq.refl` term, admits it as a transient theorem, and audits its dependency
closure. The normalized operation receipt binds the clean Git commit, machine
frontier, registry, fact, manifests, external bytes, and checked observation.

The transaction builder and settled-fact checker recognize the same driver.
They do not accept caller-authored paths, commands, proof hashes, budgets, or
admission metadata.

## Measured dispatch delta

The frozen train/development census now reports one eligible row and 137 rows
with no exact authoritative operation. It still records zero executor
invocations because it is a capability census, not an episode.

## Next boundary

Execute from this clean registration commit, prepare the typed transaction,
inject a fault after durable intent, recover it, replay the settled operation,
derive the post-frontier delta, and preserve the complete episode externally.
Only that sequence may establish the fact.

## Reproduction

```sh
python3 scripts/validate-autogenesis-operations.py
python3 scripts/fact-frontier.py --output /tmp/reflexivity-frontier.json
python3 scripts/create-autogenesis-nursery-dispatch-baseline.py --check
```
