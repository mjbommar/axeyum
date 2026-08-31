# Lane: inventory-from-authority

**Status (2026-08-31): surveying.** Auditing kernel tests whose name promises
completeness but whose body iterates a hand-written list.

Early finding: the brief's premise is partly stale. `nat`, `int`, `rat`,
`complex`, `creal` and `creal_point` all already carry an environment-derived
exhaustiveness assertion (the `unlisted` pattern). The remaining gap is being
measured.

## Landed changes

| date | change | commit |
| --- | --- | --- |
| 2026-08-31 | lane opened | — |
