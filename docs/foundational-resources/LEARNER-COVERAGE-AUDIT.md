# Learner Coverage Audit

## Purpose

This audit records whether the current foundational math example packs are
visible from learner-facing material. It is deliberately narrower than the
generated proof-upgrade dashboard: the dashboard is the mechanical source of
truth, while this file explains the current result, the coverage categories,
and the policy for future packs.

The invariant is the same as the rest of the resource buildout:

```text
untrusted fast search, trusted small checking
```

A learner page should show the finite, bounded, or computable slice Axeyum can
check, then name the replay, certificate, or theorem-horizon boundary.

## Current Result

Audit date: 2026-07-03.

Evidence:

```sh
python3 scripts/query-foundational-resources.py summary
```

Current summary:

- 125 concept rows.
- 161 non-template math packs.
- 1047 expected checks.
- 387 checked proof/evidence rows.
- 536 replay-only rows.
- 124 Lean-horizon rows.
- 161 promoted solver-reuse packs.
- 0 non-benchmark-horizon solver-reuse packs.

The generated learner dashboard reports:

```text
math example packs: 161
Learner Status Totals:
- focused: 161
```

`focused` means the pack is explicitly mentioned by at least one
`docs/learn/math/*-end-to-end.md` page. The current generated dashboard has no
`path-only`, `index-only`, or `missing` learner-status buckets for non-template
packs.

## Coverage Categories

The generator in `scripts/gen-foundational-dashboards.py` classifies pack
coverage as follows:

| Status | Meaning | Current Count |
|---|---|---:|
| `focused` | At least one non-README `docs/learn/math/*-end-to-end.md` page mentions the pack id or pack path. | 161 |
| `path-only` | Only a non-end-to-end learner page mentions the pack. | 0 |
| `index-only` | Only `docs/learn/math/README.md` mentions the pack. | 0 |
| `missing` | No learner page mentions the pack id or pack path. | 0 |

The mechanical rule is intentionally strict: broad cluster pages and the math
README can help navigation, but a pack counts as focused only when a focused
end-to-end page names it.

## What This Means

The current learner spine satisfies the Stage 2 coverage gate for existing
non-template packs:

- every pack appears in a focused lesson;
- every focused lesson is reachable from the learner index or a cluster path;
- the generated dashboard can identify future drift without a manual scan.

This does not mean every lesson has equal depth. Some pages are complete
source-to-witness walkthroughs, while others are intentionally compact because
the pack is one member of a larger proof-route family. That is acceptable when
the page still names the pack, the check shape, and the theorem or proof
horizon.

## Future Policy

For new non-template math packs:

1. Add a focused end-to-end learner page unless the pack is naturally
   inseparable from an existing focused page.
2. If using a combined page, explicitly name the pack id and explain why the
   combined story is the right learner unit.
3. Do not rely on `docs/learn/math/README.md` alone for pack coverage.
4. Keep cluster pages as navigation surfaces, not as the only educational
   explanation for a pack.
5. Run the dashboard generator and link checker before claiming R3 coverage.

Combined-page-only coverage is allowed only for packs whose source object and
proof route are best taught together, such as a tightly coupled coordinate /
affine geometry family or a shared statistics/regression workflow. Split the
page when the pack introduces a distinct proof route, trust boundary, or
consumer query shape.

## Audit Commands

Use these commands after adding or editing packs or learner pages:

```sh
./scripts/check-foundational-resources.sh
python3 scripts/query-foundational-resources.py summary
./scripts/check-links.sh
```

For a quick learner-status check after dashboards are regenerated, inspect:

```text
docs/foundational-resources/generated/learner-proof-upgrade-dashboard.md
```

The expected healthy state for the current inventory is:

- `focused`: 150;
- no `path-only`, `index-only`, or `missing` rows.

When the pack count changes, the expected focused count should change with it
unless the new pack is explicitly temporary or still below the R3 learner gate.
