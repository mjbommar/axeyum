# Lane: absence-matcher — pair an absence claim to its own sentence

<!-- plan-section: lane-status -->

**Status:** done. `scripts/check-absence-claims.py` now pairs a claim with the
names in its OWN unit (Markdown record, then sentence) rather than its whole
block. Bare unexpirable claims **250 -> 122** on the real tree, budget lowered
to match, and all 11 declarations of the 8 known-stale claims still caught.
ADR-1190.

## The deficiency

The census budget had been raised twice (141 -> 249) and was RED at 250 —
tracking NOISE, not claims. A claim phrase fired on one sentence of a
multi-paragraph block and `DECL_RE` harvested every `Root.name` in the WHOLE
block as that claim's subject; most were cited as PRESENT evidence in a
neighbouring sentence. Worst single site: **93** candidates out of one Markdown
table. Two independent hand audits rejected the surplus (55 of 70 on
2026-08-27; every one of the remaining 249 on 2026-08-31), and the second
recommended this fix and scoped itself out of it.

## What landed

- **Unit-granular association.** A record first (Markdown table row or list
  item), then a sentence within it. Sentence boundary is `.`/`!`/`?` + space,
  deliberately **not** `:` or `;` — two of the eight known-stale claims name
  their subjects across exactly those punctuation marks. A wrapped item's
  continuation lines stay with the item.
- **A marker only silences a claim whose subject it NAMES** (exact, then
  spelling-normalized). Required by the change above: with N sites per block,
  one `annotated` flag would let a marker for X cover a claim about Y. Exposed
  4 real sites, which is why the honest figure is 122 rather than 118.
- **Registered the checker in the aggregate gates.** `check.sh` ran only
  `absence-claims-tests` — the unit tests, on synthetic fixtures — and
  `just check` never named `absence-claims` at all, so all 39 markers in the
  real tree were checked only when a human typed the recipe. ADR-1170's defect,
  one registration below ADR-1170's own retrospective.

## Measurement

Fresh `kernel_declaration_projection` (2,636 declarations, floor 1,750; binary
verified fresh — kernel sources `diff -rq` identical to the shared checkout and
none newer than the binary):

| | sites | named | annotated | **bare** | worst site |
| --- | --- | --- | --- | --- | --- |
| before | 987 | 287 | 37 | **250** | 93 candidates |
| after | 1,054 | 154 | 32 | **122** | 8 candidates |

Regression: 11/11 declarations of the 8 corrected stale claims still attributed,
pinned from `335cb3661^` in `scripts/tests/fixtures/absence-stale-claims/`.
Break/restore through the real gate: stale `Nat.clog` text restored -> exit 1,
123 bare, site attributed `('Nat.clog',)`; restored -> exit 0, 122.
`mutation_controls.py absence-claims` exits 0, 45 tests, every mutation a
`killed N`.

## Landed changes

| date | commit | what |
| --- | --- | --- |
| 2026-08-31 | (this lane) | pair a claim to its own sentence, not its whole block; budget 249 -> 122; 8-claim fixture regression; 7 mutations |
| 2026-08-31 | (this lane) | register the checker itself in `check.sh` and `just check`; ADR-1190 |
