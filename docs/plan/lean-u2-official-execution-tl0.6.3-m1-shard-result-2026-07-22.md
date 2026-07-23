# Lean U2 TL0.6.3 M1 child-shard derivation result

Status: **accepted derivation; no shard executed; no parity credit**

Date: 2026-07-22

Target: Lean `v4.30.0` at
`d024af099ca4bf2c86f649261ebf59565dc8c622`.

## Result

The source-first
[M1 plan](lean-u2-official-execution-tl0.6.3-m1-shard-plan-2026-07-22.md)
was committed and pushed at `26f4378afd53981a00dac44d619c4b3638600eb5`
before the derivation ran. The implementation and first generated authority
were then committed and pushed at
`597c0fa7bd56731eddab409ff25220368e020858`.

The accepted result is:

| Quantity | Derived value |
|---|---:|
| registered U2 cases | 3,723 |
| official selection-set bindings | 8 |
| official attempt bindings | 111 |
| distinct exact ordered memberships | 5 |
| factored membership case occurrences | 18,277 |
| physical child shards | 289 |
| selection-expanded shard occurrences | 461 |
| attempt-expanded shard occurrences | 6,451 |
| unique selected-case union | 3,723 |
| M1 outcomes / pairs / parity credit | 0 / 0 / 0 |

The five memberships contain 3,678, 3,723, 3,477, 3,722, and 3,677 cases and
partition into 58, 59, 55, 59, and 58 shards respectively. Each shard is a
contiguous slice of at most 64 names in the exact parent selection order.

Three pairs of selection identities share exact ordered membership:

- default all and default `-E foreign`;
- full-Lake all and full-Lake `-E foreign`; and
- default and full-Lake sanitizer selections.

This is exact membership factoring, not set-, count-, profile-, or
digest-prefix-based conflation. All eight selection identities and all 111
attempt identities remain separately bound to the shared physical plans.

## Exact artifacts

| Artifact | SHA-256 / logical seal |
|---|---|
| [`lean-u2-official-child-shards-v1.json`](lean-u2-official-child-shards-v1.json) | physical `6a2ec0b3edd353f3deb76e805052d5d2465ed1c9dd59cf221b0d175d0ce5e3e9`; record `923df740b24b2dd1ec05e277bcfaec43681d5fd4d6fbdf1a67ebd6a6144e6f28` |
| generated [JSON](generated/lean-u2-official-child-shards.json) | `4854ab14686b5a4c8cee625d5655ef83deb0d1b5bae012d2d2fce7ef0a5001e8` |
| generated [Markdown](generated/lean-u2-official-child-shards.md) | `a2df322aa1622c7b1049867793ab8cbc449ad576fed6eecb45a79d696c45ea95` |
| `scripts/gen-lean-u2-official-child-shards.py` | `e1f6bb869fe5fb6ec740589d6e3b0f514e6efbc5604b0010bdd9dd44e10434a3` |
| `scripts/tests/test_lean_u2_official_child_shards.py` | `f402ec4c885344900c090e69a0ad3a585f3df595b721632be880067b85a83d65` |

The authority also binds and semantically validates the exact U2 registration,
official CI profile, and amended R3 result authorities and their frozen
validator sources. The 3,723-case union and every overlapping membership are
reconstructed from those parents; the generator does not consult a Lean
checkout or execute CTest.

## Historical singleton treatment

`compile/534.lean` remains present in every applicable membership. Its four M0
process attempts, two completed attempts, one pass, and one failure are retained
as a separate `historical-local-singleton-only` annotation. They do not
complete an M1 shard because the M1 shard boundaries did not exist before that
execution, and they do not complete a parent profile or provider. Re-executing
the singleton cannot increase unique population coverage.

## Validation

The focused suite passes nine tests. It verifies deterministic regeneration,
exact membership factoring, complete ordered partition closure, the 64-case
bound, all 111 not-run attempt bindings, historical annotation, and direct
`--check` operation. Resealed mutations reject:

- physical input, validator-source, and parent semantic drift;
- missing or reordered shards;
- oversized, offset-mutated, duplicated, or reordered case slices;
- selection/membership and attempt/selection misbinding;
- an invented outcome or M1 completion from the historical singleton; and
- positive terminal claims or nonzero parity credit.

Reproduction:

```sh
python3 -m unittest scripts.tests.test_lean_u2_official_child_shards -v
python3 scripts/gen-lean-u2-official-child-shards.py --check
```

## Non-claims

This result proves a complete deterministic scheduling projection over the
current official U2 selections. It does **not** prove that any new case ran,
that a full official attempt/profile/provider completed, that Axeyum supports a
case, that a paired result exists, that a shard is representative, or that Lean
functional, assurance, performance, ecosystem, or maintained parity improved.
U2 remains `bounded_profile`; all U0-U9 terminal denominators, A0-A11 complete
axes, paired terminal cells, and G1-G10 gates remain open.

## Handoff

The next TL0.6.3 execution step must be source-first and separate. It must name
the exact derived shard(s), avoid treating shard zero as representative,
preregister provider/executable/configuration/environment/resource/attempt/
completion/retry identities, and retain valid, incomplete, and invalid runs
separately. Native surface classification and matched Axeyum execution remain
TL0.6.4/TL0.6.5 work.
