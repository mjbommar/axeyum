# Lane: retrieval-gate

**Status:** in progress — auditing why `shape_search` adoption sits at 7% while
mutation testing sits at 42%, and wiring the retrieval side's gate.

Working note (first commit, incomplete): re-measurement over
`docs/plan/status/*.md` (429 files, `/usr/bin/grep -l`) reproduces the brief
exactly — `shape_search` 30 (7.0%), `mutation|mutant` 180 (42.0%), `cargo` 238
(55.5%).
