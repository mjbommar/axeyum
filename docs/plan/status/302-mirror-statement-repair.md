# Lane: mirror-statement-repair -- 19 mirrors got their proposition back, and the pin was better than anyone thought

<!-- plan-section: lane-status -->

**Lane block (`DONE -- 23 facts repaired, gate registered in both aggregate
gates, 9 guards each mutation-verified`, mirror-statement-repair, 2026-08-29).**

## Headline

| | before | after |
| --- | --- | --- |
| `ml430` mirrors whose `formal.statement` is a kernel rendering | 19 | **0** |
| `ml430` mirrors whose statement matches its preregistered hash | 358 / 362 | **362 / 362** |
| gate detecting either | none | `check-mirror-statement-fidelity.py`, both gates |
| guards, each killed by exactly one control | -- | **9 / 9** |
| false-positive controls | -- | 4 (one over the real ledger) |

The reported 19 is exact and reproduces. The restore source is **not** the
nursery manifest the brief and the design review both expected -- it is a
**content hash**, which makes the repair verifiable rather than merely
corroborated.

## Step 0 -- re-measurement, reproduced then widened

```
total facts 2114 | ml430 374 | non-ml430 1740
  starts-theorem   19        x0-binder  18        Eq.{  13
  AxNat            19        ascii-arrow 18
union flagged by ANY of twelve signatures: 19
baseline signature (starts-`theorem ` | AxNat | AxInt): 19
EXTRA beyond baseline: 0
```

I widened the detector to twelve independent kernel-rendering signatures --
`AxRat`, `AxReal`, `CReal`, `Eq.{`, an `(xN :` binder, a leading `def `/
`axiom `, `Sort.{`/`Type.{`, an ASCII ` -> ` arrow -- and **the union is the
same 19 files.** No twentieth fact exists under any wider signature.

**Positive control.** The 355 unflagged mirrors carry Mathlib surface syntax
(`∀ (a b c : ℤ), a + b + c = a + (b + c)`), so the detector is not flagging
everything.

Two sub-signatures are individually INCOMPLETE and each would have missed
`Nat.not_coprime_zero_zero`, which is a closed statement and therefore has
neither a binder nor an arrow. Only `starts-theorem ` and `AxNat` are complete
over this set -- which is the reviewer's original pair, arrived at
independently.

## The restore source: a preregistered HASH, not a transcription

`artifacts/autogenesis/nursery-v*.json` does **not** hold a pinned `type` per
row. Its entries are `fact_id` / `partition` / `family` / `proof_shape` /
`provenance_class` and nothing else. Following the brief literally would have
found nothing.

What does exist is better. `artifacts/autogenesis/mathlib-nat-int-fact-catalog-v1.json`
(and `nursery-v2-extension.json` for the later draws) pins
`source_statement_sha256` per fact -- a **SHA-256 of the Mathlib statement
text**. So the check is cryptographic:

```
sha256(creating-commit `formal.statement`) == preregistered source_statement_sha256
   ->  19 of 19
```

Detail moved to [`../notes/302-mirror-statement-repair.md`](../notes/302-mirror-statement-repair.md).

