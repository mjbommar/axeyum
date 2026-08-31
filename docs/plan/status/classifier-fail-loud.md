# Lane: classifier-fail-loud

## Status

**In progress (2026-08-31).** Making a curriculum-bucket MIS-attribution loud in
`scripts/measure-curriculum-kernel-coverage.py`.

Established so far:

- The classifier is registered in **neither** `scripts/check.sh` nor the
  `justfile` (`/usr/bin/grep -rn curriculum scripts/check.sh justfile` returns
  three unrelated comment lines). It runs only when a lane runs it by hand,
  which is why both ADR-1140 and ADR-1205 were found by lane inspection rather
  than by a gate.
- `kernel_declaration_projection` emits `kernel.environment()` rows and carries
  no source module.

## Landed changes

(none yet)
