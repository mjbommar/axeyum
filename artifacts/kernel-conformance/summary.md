# Lean Kernel Arena conformance -- both halves

**Generated** by `scripts/check-kernel-conformance.py --refresh`. Do not
edit: every number here is re-derived from `results.tsv` by the gate, and a
hand edit fails G8.

- corpus: `https://github.com/leanprover/lean-kernel-arena` at `abc55357aee17c59dfdbf39c8a2e19739e23dd10`
- test tarball: `https://arena.lean-lang.org/lean-arena-tests.tar.gz`
  sha256 `7e396d5de90e8871c9b1d7e2931f3efaba303056cdfd93e65f9ae1de628bf326`
- cases scored: 186 (digest `85fcd0166965743839f26f1e9ff179112d0ea6471a76b4c283c561149e7cd6f1`)
- measured: 2026-09-05T11:26:41Z

The corpus's `either` corner cases are not in the published tarball and are
not scored here. Cases larger than 10 MB (mathlib, std, cslib, cedar, init)
are excluded by upstream from the same tarball.

## Scores

| mode | half | total | correct | wrong | declined | no verdict |
|---|---|---:|---:|---:|---:|---:|
| full | accept | 113 | 108 | 4 | 0 | 1 |
| full | reject | 73 | 69 | 2 | 2 | 0 |
| parse-only | accept | 113 | 110 | 2 | 0 | 1 |
| parse-only | reject | 73 | 21 | 50 | 2 | 0 |

## The control

`parse-only` is the same reader with the trusted gate's verdict discarded
(`census_ndjson`). It is the arena's own control reproduced in-tree, and it
is why the accept half alone is not a result.

- reject half: full mode 69, control 21 -- a gap of **48**.
- so **21** of the reject half is
  decided by the reader and recursor regeneration, and the remaining
  **48** by the trusted gate. A reject-half score quoted without this
  split does not say which layer earned it.

## Divergences

Every row below is listed in [`docs/plan/lean-divergences.md`](../../docs/plan/lean-divergences.md); `scripts/check-lean-divergences.py`
fails if one is not.

| case | expected | our verdict | class |
|---|---|---|---|
| `core/level-index-out-of-order` | accept | reject | `malformed` |
| `core/sparse-name-index` | accept | reject | `malformed` |
| `perf/app-lam` | accept | timeout | `timeout` |
| `tutorial/012_nonPropThm` | reject | accept | `ok` |
| `tutorial/019_tut06_bad01` | reject | accept | `ok` |
| `tutorial/107_unitEta1` | accept | reject | `kernel:DeclarationValueMismatch` |
| `tutorial/108_unitEta2` | accept | reject | `kernel:DeclarationValueMismatch` |
| `tutorial/141_falseFromUnsafe` | reject | decline | `unsupported:declaration-unsafe-or-partial` |
| `tutorial/142_falseFromPartial` | reject | decline | `unsupported:declaration-unsafe-or-partial` |
