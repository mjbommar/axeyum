# Lean recursive induction hypotheses: M0 source/wire freeze

Status: complete; M1 shared representation is next

Date: 2026-07-22

Parent:
[TL2.12 execution plan](lean-recursive-induction-hypotheses-tl2.12-plan-2026-07-22.md)

Decision:
[ADR-0353](../research/09-decisions/adr-0353-preregister-lean-recursive-induction-hypotheses.md)

Machine registration:
[`lean-recursive-induction-hypotheses-v1.json`](lean-recursive-induction-hypotheses-v1.json)

## Result

M0 freezes the exact semantic contract, existing product baseline, official
computation source, two root-specific format-3.1 streams, independent wire
inventories, future native/mutation/generated populations, resource policy, and
stop conditions before any Axeyum kernel or importer semantic change.

The claim boundary is exact:

- pinned Lean compiled the final source twice;
- pinned `lean4export` produced each selected stream twice with byte-identical
  output;
- the independent Python reader inventoried the official wire forms;
- Axeyum did **not** import, admit, or compute either new stream;
- no new kernel result, importer result, `CompletedImport`, generated summary,
  or Lean-parity credit is present.

## Frozen source

[`lean-v4.30-recursive-ih-computation.lean`](fixtures/lean-v4.30-recursive-ih-computation.lean)
is 1,422 bytes / 48 lines at SHA-256
`ebf95e789906c05a27db5eb55b29a8fe7c2429969712099b6aca4905dc88b06d`.
It defines the exact single-family `MiniVector` and `MiniAcc` shapes and uses
their recursors explicitly rather than relying on an inferred pattern-match
translation:

- `vectorHeight` supplies the indexed recursive tail's IH and
  `vectorHeightComputes` closes the one-element computation by `rfl`;
- `accProperty` supplies the higher-order two-binder field's function-shaped IH
  and `accPropertyComputes` closes its computation by `rfl`.

Both recursor consumers are `noncomputable`: the evidence is kernel reduction,
not executable code generation. Their transparent bodies and the two `rfl`
theorems still force the intended recursor iota rules.

The final source compiled twice with exit 0 and empty stdout. Maximum RSS was
462,868 and 462,912 KiB under one Lean worker and the 3/4 GiB systemd policy.

## Pre-freeze source calibration

Two draft failures occurred before the source hash and machine contract were
frozen:

1. the first `MiniVector` minor supplied four explicit lambdas, while pinned
   Lean exposes the constructor index as an implicit minor-premise binder and
   expects three explicit arguments (`element`, `tail`, `IH`);
2. after correcting that binder, the kernel accepted the term but the runtime
   code generator declined the custom indexed recursor, so the logical
   recursor consumers were correctly marked `noncomputable`.

No expectation, hash, or Axeyum result existed at either failure. The final
source then passed both `rfl` computations before registration.

## Frozen official streams

| Root | SHA-256 | Bytes | Records | N/L/E/D | Blockers | Export RSS KiB |
|---|---|---:|---:|---|---|---|
| `vectorHeightComputes` | `1ab5a38b50d4d2c7ba01ef2831bb5af5d3c56ce1b9879c1942070519a9f6df19` | 15,944 | 284 | 60/4/211/8 | `inductive-recursive-indexed` | 703,092 / 706,180 |
| `accPropertyComputes` | `3cb06283f1e757d79d28335dfe77ccd00231a8d323c2310dddced6473933c003` | 17,722 | 314 | 67/3/232/11 | `inductive-recursive-indexed`, `inductive-reflexive` | 704,284 / 705,276 |

`N/L/E/D` means name, nonzero-level, expression, and declaration-record counts.
The retained aggregate is 33,666 bytes, below the registered 1 MiB per-stream
and 2 MiB aggregate limits.

The independent inventories freeze the target metadata:

- `MiniVector`: one parameter, one index, zero nested occurrences,
  `isRec=true`, `isReflexive=false`; its recursor has one motive, two minors,
  and rule field counts `[0, 3]`;
- `MiniAcc`: two parameters, one index, zero nested occurrences,
  `isRec=true`, `isReflexive=true`; its recursor has one motive, one minor, and
  rule field count `[2]`.

The selected theorem is the final declaration in each stream. The Vector and
Acc exports are separate so later admission/computation evidence cannot leak
between roots.

## Frozen implementation contract

For `u : Pi xs, I params indices`, M1--M3 must preserve exactly:

```text
IH          = Pi xs, motive indices (u xs)
rule value  = fun xs => I.rec params motive minors indices (u xs)
```

All constructor fields precede all IHs; both groups preserve source order. One
WHNF telescope-tail classifier must drive minor types and rule right-hand
sides. Field structure and kernel checking remain authoritative;
`isReflexive` is descriptive metadata, not an admission permission bit. Direct
recursion remains the empty-telescope/empty-index control.

The registration also freezes:

- 14 native case identities;
- 12 mutation-family identities;
- the future >=512-case, two-run, byte-identical generated grammar contract;
- the completed 840-case strict-positivity grammar as mandatory;
- direct-recursive, construct-matrix, and completion-only import controls;
- 13 stop conditions and exact tool/resource/command pins.

## Fail-closed validation

[`check-lean-recursive-induction-hypotheses.py`](../../scripts/check-lean-recursive-induction-hypotheses.py)
recomputes source and baseline hashes, both complete stream censuses, selected
roots, target inductive/recursor metadata, retention bounds, and repository
toolchain identity. It rejects premature Axeyum product fields outright.

Ten mutation/contract tests cover:

- source hash and expected-normal-form drift;
- stream hash/size/record/root drift;
- target inductive and recursor metadata drift;
- pin, resource, and command drift;
- semantic-contract and claim-limit drift;
- case and mutation population/order/identity drift;
- generated grammar, mandatory positivity control, and stop-condition drift;
- historical baseline-fixture drift;
- any premature kernel result or other Axeyum observation.

The checker and tests are now mandatory in `parity-docs` and the plain-shell
aggregate check.

## Next gate

M1 adds the shared WHNF recursive-field classifier/reopener and stable field
metadata while retaining the existing recursive-indexed and reflexive feature
declines. Existing direct recursion must route through that representation with
registered type/rule/computation identity before M2 may widen admission. No
importer policy changes occur in M1.
