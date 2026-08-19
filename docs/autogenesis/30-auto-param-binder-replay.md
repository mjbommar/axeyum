# Checked `autoParam` binder replay

Date: 2026-08-19

## Result

All **138 of 138** frozen Mathlib v4.30 train/development statements now have
an independently checked, proof-free producer boundary. The original exact
route remains unchanged for 128 statements. The ten former typed declines use
the separately versioned binder-normalization route settled by ADR-0485 and
ADR-0486.

The exact-commit replay produced:

- 128 v1 receipts with no transport normalization;
- 10 v2 receipts carrying complete normalization evidence;
- 152 typed definition abstractions;
- 164 checked `autoParam` rewrites across eight constructor/recursor names;
- zero selection declines; and
- zero held-out reads, proof-producer executions, proof-body requests, or
  ledger writes.

The immutable external observation has semantic identity
`49c36e75fcaedef1f76ee1b99268903cc2a10192a549c8b835acf4e1c1f181ec`
and file identity
`969b53a44ed31166b94c611af406ab46c07f5be2b7e1aa9a5ceff1aac78dc5c5`.
It was produced from committed tooling at `2f2fe9b0c` and reproduced the prior
exploratory observation byte-for-byte.

## What changed

The negative control mattered. Normalizing saturated `autoParam α tactic`
applications in declaration types alone left coverage at 128/138. The ten
closures still reached `Lean.Syntax` through binder annotations embedded in
recursor-rule right-hand sides.

The accepted v3 policy expands the rewrite surface only to `Lam` and `Pi`
binder domains inside those rules. Before emitting anything, the source kernel
checks the exact Lean 4.30 `autoParam` definition, infers both original and
normalized declarations and rules, and proves them definitionally equal.
Ordinary definition values and direct value-position applications remain
untouched. Dependency selection and serialization consume the same normalized
expressions, so the receipt cannot describe one closure while emitting another.

Each v2 receipt binds the source `autoParam` identity, rewrite count, and every
changed declaration's source content, normalized content, and normalized
dependency identities. The checker also requires each normalized identity to
be the one actually retained and rejects theorem, axiom, opaque, or quotient
retention.

## Flywheel significance

Bottom-up, the proof-search input boundary is no longer the bottleneck for this
population: every unsealed statement can enter a fresh kernel without importing
its answer. The transport remains versioned and qualified to Lean 4.30, rather
than becoming a general license to erase elaborator metadata.

Top-down, the next question is now measurable: **given all 138 checked goals,
what can bounded proof producers establish autonomously?** The first run should
stay entirely within train/development, freeze producer grammars and budgets,
and emit structured declines for unsupported proof shapes. Those declines then
select the next reusable capability work. Held-out remains sealed until that
selection policy and its resource budgets are frozen.

This result proves no source theorem. It establishes only the checked boundary
on which untrusted proof search may begin.

## Reproduction

```sh
python3 -m unittest scripts.tests.test_check_autogenesis_auto_param_binder_replay
python3 scripts/check-autogenesis-auto-param-binder-replay.py
cargo run -p axeyum-lean-import --example type_slice_replay -- \
  --auto-param-binders-v3 \
  --archive /nas3/data/axeyum/autogenesis/coverage/26fcc2c2f-mathlib-v4.30.0-reflexivity-train-development-v1 \
  --mapping /nas3/data/axeyum/autogenesis/coverage/26fcc2c2f-mathlib-v4.30.0-reflexivity-train-development-v1/mapping.json \
  --output observation.json
```
