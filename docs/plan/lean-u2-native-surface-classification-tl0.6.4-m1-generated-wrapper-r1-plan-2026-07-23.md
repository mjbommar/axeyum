# Lean U2 TL0.6.4 M1 R1 plan — generated registration-wrapper boundary

Status: **preregistered correction; no M1 implementation, refined case, native
outcome, pair, or parity credit exists**

Date: 2026-07-23

Parent:
[M1 pinned-content plan](lean-u2-native-surface-classification-tl0.6.4-m1-plan-2026-07-23.md).

## 1. Discovery

The source-first command/reference audit found that normalized pile commands
name `$LEAN_ROOT/tests/with_stage1_test_env.sh`. That path is a configured build
artifact, not a Git-tracked file at pinned Lean commit
`d024af099ca4bf2c86f649261ebf59565dc8c622`; it is therefore absent from the
7,004-file U2 content manifest. The tracked source inputs include
`tests/with_env.sh.in`, `tests/env.sh.in`, `tests/CMakeLists.txt`, and
`tests/util.sh`.

M1 cannot inspect bytes that do not exist in its source-only population. It
must not follow a normalized generated path as if it were a tracked file,
silently drop it, or materialize an unregistered build tree.

## 2. Corrected M1 contract

The M1 implementation must:

1. retain the exact generated wrapper path from each normalized registration
   command as `generated-reference`;
2. prove that the path is absent from the pinned tracked-content manifest;
3. inspect the tracked configuration/template inputs when they occur in the
   7,004-file census, recording their ordinary content signals without
   pretending that they are byte-equal to a configured output;
4. add a stable `generated-wrapper-not-materialized` residual to every affected
   case projection and to aggregate accounting;
5. prohibit the generated reference or template signal from adding a new case
   surface in M1; and
6. leave exact configured-wrapper bytes, substitutions, executable identity,
   and reachability to M2 generated-artifact dependency closure.

`content_refinement = complete-census` means complete inspection of the frozen
tracked-source population, not inspection of generated outputs. The separate
generated residual remains mandatory and prevents M1 or M3 from silently
claiming exact wrapper closure.

The existing M1 statement that exact registration wrappers are inspected is
therefore narrowed to exact **tracked** wrappers. Generated wrapper references
are fully inventoried but not content-inspected.

## 3. Mutation teeth

Focused tests must reject:

- a generated reference treated as a tracked file or exact content hit;
- a generated reference omitted from an affected case;
- a generated wrapper promoted into an M1 surface;
- substitution of a template path for the generated path;
- loss or false resolution of the aggregate residual; or
- any claim that M1 completed generated-artifact or module dependency closure.

This correction changes no file/case denominator, execution state, or credit.
M1 remains source-only and non-executing; M2 owns exact generated-wrapper
materialization and reachability.
