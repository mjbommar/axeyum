# Lean mutual inductive groups: M0 source/wire freeze

Status: complete; M1 group representation and singleton delegation are next

Date: 2026-07-22

Parent:
[TL2.13 execution plan](lean-mutual-inductive-groups-tl2.13-plan-2026-07-22.md)

Decision:
[proposed ADR-0354](../research/09-decisions/adr-0354-preregister-lean-mutual-inductive-groups.md)

Machine registration:
[`lean-mutual-inductive-groups-v1.json`](lean-mutual-inductive-groups-v1.json)

## Result

M0 freezes the ordered group rule, existing product baseline, official
computation source, two root-specific format-3.1 streams, independent wire
inventories, future native/mutation/generated populations, resource policy,
and stop conditions before any Axeyum kernel or importer semantic change.

The claim boundary is exact:

- pinned Lean compiled the final source twice;
- pinned `lean4export` produced each selected stream twice with byte-identical
  output;
- the independent Python reader inventoried both official groups and every
  exported recursor record;
- Axeyum did **not** import, admit, or compute either new stream;
- the historical mutual stream still has only its registered
  `Unsupported(inductive-mutual)` product observation;
- no new kernel result, importer result, `CompletedImport`, generated summary,
  or Lean-parity credit is present.

## Frozen source

[`lean-v4.30-mutual-inductive-computation.lean`](fixtures/lean-v4.30-mutual-inductive-computation.lean)
is 1,676 bytes / 66 lines at SHA-256
`d04059e05cbb15d74c6dc526c63e2ac028dfb4b0fe604c9dd3eebdc963e06404`.
It defines two independent parameterized groups and invokes the generated
recursors explicitly:

- `EvenTree`/`OddTree` and `evenHeight` force the transition
  `EvenTree.rec -> OddTree.rec -> EvenTree.rec`;
- indexed `EvenVec`/`OddVec` and `oddVecHeight` force
  `OddVec.rec -> EvenVec.rec -> OddVec.rec` while preserving the recursive
  field's index;
- `crossFamilyComputes` and `indexedCrossFamilyComputes` both close by `rfl`
  at `MiniNat.succ (MiniNat.succ MiniNat.zero)`.

The final source compiled twice at exit 0 in 460 and 220 ms. Maximum RSS was
474,312 and 474,740 KiB under one Lean worker and the registered 3/4 GiB
systemd policy. Both runs produced the same OLEAN SHA-256:
`b2582c150c5901728a871919e1c04922f44c11ddeba1a8a446189b6c4d604aba`.

## Frozen official streams

| Root | SHA-256 | Bytes | Records | N/L/E/D | Blockers | Export RSS KiB |
|---|---|---:|---:|---|---|---|
| `crossFamilyComputes` | `5013aff1165c8a50a63c54cd946ab2b489d0edfee7e0862bc53b061eabac0070` | 18,827 | 318 | 60/4/246/7 | `inductive-mutual` | 711,496 / 711,984 |
| `indexedCrossFamilyComputes` | `fe867639eeed25db9672730b092db32a49b79e82c6c59c386d9ff0e6a48b3787` | 21,455 | 374 | 72/4/290/7 | `inductive-mutual`, `inductive-recursive-indexed` | 712,284 / 712,428 |

`N/L/E/D` means name, nonzero-level, expression, and declaration-record counts.
The retained aggregate is 40,282 bytes, below the registered 1 MiB per-stream
and 2 MiB aggregate limits. Each selected theorem is the final declaration in
its stream.

Each family has one shared parameter and two constructors. The tree families
have no indices; the vector families each have one. Every recursor binds two
motives and four minors. Tree rule field counts are `[0, 1]` for `OddTree.rec`
and `[1, 1]` for `EvenTree.rec`; both vector recursors carry `[0, 2]`.

## Source order is not wire recursor order

The group family order in both exports is source order:

```text
[EvenTree, OddTree]
[EvenVec, OddVec]
```

The wire `recs` arrays are dependency-ordered in the opposite direction:

```text
[OddTree.rec, EvenTree.rec]
[OddVec.rec, EvenVec.rec]
```

This does not change the semantic ordering rule: motives remain in family
order, and minors remain in family-then-constructor order. It does constrain
M4 importer comparison: exported recursors must be matched by checked recursor
name and owned constructor rules. Array position is descriptive wire order and
must not be used as family identity. The machine registration and mutation
tests freeze this distinction.

## Frozen implementation contract

M1--M4 must preserve one atomic ordered group:

```text
shared parameters
  -> motives in family order
  -> minors in family then constructor order
  -> owner-family indices and major
```

For `u : Pi xs, I_j params recursive_indices`, the corresponding premise and
rule argument are:

```text
IH          = Pi xs, motive_j recursive_indices (u xs)
rule value  = fun xs =>
                I_j.rec params all_motives all_minors
                  recursive_indices (u xs)
```

Group-wide positivity ranges over every family before provisional insertion;
all family recursors self-check before atomic publication. Mutual `Prop` groups
eliminate only to `Prop` and receive no K-like reduction. `add_inductive` must
delegate to the group implementation without single-family identity or
behavior drift.

The registration also freezes:

- 18 native case identities;
- 16 mutation-family identities;
- the future >=640-case, two-run, byte-identical group grammar contract;
- the completed 768-case recursive and 840-case positivity controls;
- construct-matrix, declaration-identity-v1, and completion-only import
  controls;
- 15 stop conditions and exact tool/resource/command pins.

## Fail-closed validation

[`check-lean-mutual-inductive-groups.py`](../../scripts/check-lean-mutual-inductive-groups.py)
recomputes source and baseline hashes, both complete stream censuses, selected
roots, family/recursor metadata and ordering, retention bounds, and repository
toolchain identity. It rejects premature Axeyum product fields outright.

Eleven mutation/contract tests cover:

- source hash and expected-normal-form drift;
- stream hash/size/record/root drift;
- group family order and family metadata drift;
- dependency-ordered wire recursor identity, count, and rule metadata drift;
- pin, resource, and command drift;
- semantic-contract and claim-limit drift;
- case and mutation population/order/identity drift;
- generated grammar, mandatory controls, and stop-condition drift;
- historical baseline fixture and outcome drift;
- any premature kernel result or other Axeyum observation.

The checker and tests are mandatory in `parity-docs` and the plain-shell
aggregate check.

## Next gate

M1 adds the ordered group/family representation and one transactional scaffold,
then routes `add_inductive` through a one-family group while retaining the
existing mutual policy decline. Existing direct-recursive declaration
identities, recursor types/rules, computations, errors, and generated summaries
must remain exact. M1 also closes typed empty-group, parameter/universe mismatch,
and name-collision preflight failures. It does not widen mutual admission or
change importer policy.
