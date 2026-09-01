# Lane: creal-split-2 — generate the `STEPS` table, migrate the self-contained modules

<!-- plan-section: lane-status -->

**Opened** (`WIP`, creal-split-2, 2026-09-01). Continues
[creal-split](creal-split.md) /
[ADR-1512](../../research/09-decisions/adr-1512-per-module-name-registries-behind-the-crealprelude-facade.md).

Two deliverables:

- **Slice D — generate the table.** Make `requires`/`provides` derived from
  the measured graph rather than hand-written, so the preflight cannot be
  silently disarmed on an unlisted edge. `scripts/creal-declare-deps.py
  --strict` exits 2 today because the hand-written table names only 3,934 of
  4,831 real `requires` edges (977 missing across 175 of 211 steps).
- **Slice E — migrate the 15 self-contained modules** (76 fields) out of
  `CRealPrelude` into per-module registries behind the ADR-1512 facade.

**Before-snapshot, base commit `5c8eaf7b8` merged with local `main`
(`a503a9241`).** `target/release/examples/kernel_declaration_projection`
SHA-256
`576296bf531513e04749c77fb2162f374e3006cb837355ee0f06c7721ecd0c87`,
14,673 rows — the same digest the previous lane pinned. `creal.rs`
**17,171** lines.

The projection digest is the invariant: every slice must reproduce it
byte-for-byte, or the slice is not done.

<!-- plan-section: landed-changes -->

| 2026-09-01 | (this commit) | Lane opened; status stub with the before-snapshot digest. |
