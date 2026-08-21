# Proof-isolated Euclidean construction decline

Date: 2026-08-20

## Result

The first clean construction attempt compiled under pinned Lean 4.30 and
Axeyum's kernel admitted its 253-declaration root closure. The authored theorem
had the intended name and statement, but its kernel-derived axiom footprint was
`[propext]`, not empty. The proof-isolation contract therefore stopped the
increment after one of two planned fresh reconstructions.

No second reconstruction, public Euclidean lift, exact target submission,
executor call, receipt, fact transition, evaluation credit, or ledger write
occurred. The theorem is not accepted support.

## What was learned

The three preregistered computation roots remain independently audited with
empty footprints. The new theorem's direct dependency set additionally names
ordinary arithmetic and control theorems, including `Nat.sub_add_cancel`,
`dif_pos`, and `dif_neg`. At least one dependency path outside the three roots
reaches `propext`.

That is narrower than “the constructive equation needs `propext`.” It says
only that this first independently authored proof closure does. The next safe
question is which exact direct dependencies carry the assumption. Answering it
requires an importer-only footprint audit, not reading their proof terms and
not guessing by rewriting the source until a checker turns green.

## Isolation and evidence

The authored source is
[`autogenesis_div_mod_go_reconstruct.lean`](../../scripts/lean/autogenesis_div_mod_go_reconstruct.lean).
It uses no proof search and was written from the 13-statement capsule without
opening upstream theorem bodies, olean values, or proof-bearing NDJSON.

The proof-bearing failed stream remains model-inaccessible in a read-only
external pack. Git retains only its identity, the independently readable
import summary, the exact stop state, and mutation-tested checks. The external
manifest SHA-256 is
`f4dfdeec6ec422bf63748e4a6629d128d3b8487d82da9fb2df92d8db96312601`.

## Next boundary

Preregister one importer-only audit of the 15 direct theorem dependencies in
the frozen failed stream. The audit may report identities and kernel-derived
footprints but may not display proof terms. No revised theorem reconstruction
is authorized until that audit partitions the dependency set into empty and
assumption-bearing roots.

## Verification

```sh
python3 scripts/check-autogenesis-euclidean-proof-decline.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_euclidean_proof_decline
```
