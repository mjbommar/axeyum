# Notes: 347-vocab-two-writers

Detail moved out of [`../status/347-vocab-two-writers.md`](../status/347-vocab-two-writers.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**Mutation kill sets, as measured** (baseline green, 18 tests, sweep exit 0,
**no survivors**): KEYS top-level 1, KEYS nested 1, KEYS non-object 1, KNOWN
unclassified 1, KNOWN stale 1, READS 1, **RUNS comparison 4**, RUNS deletion 1,
CTRL 1, **OWNER 2**. The two multi-kills are structure, recorded at the
registration site: `CTRL` is *defined* as "the RUNS machinery must reject a
planted writer", so blinding one comparison blinds both, and that mutant also
stops the post-finding restore two further cases assert.

**The controls found a real defect in the gate on their first run.**
`SECOND_WRITER` dropped `bridge_provenance`/`row_digest` **by name**, so
against any artifact without those keys it rewrites the file byte-identically
and is accepted — the control proving `RUNS` can fail would itself have been a
check that cannot. Latent the moment a second artifact is registered. It now
drops the artifact's own `required_keys[-1]`. `KNOWN` separately flagged the
control file for naming the artifact in a fixture string; that literal is built
from parts now.

**Gates.** Holdout isolation
`held_out=116|files_scanned=1107|settled=0|references=0|PASS`, exit 0,
unchanged — no held-out row was read or written.
`gen-autogenesis-nursery-refill.py --check` exit 0 (was red since 04:23).
Ownership gate `artifacts=1|producers_run=5|fails=0|PASS` exit 0.
`gen-adr-index.py` 621 rows, exit 0.

**Not done, deliberately.** The registry guards ONE artifact. Every other
generated file under `artifacts/` is unguarded; each addition must run its
producers, so the list should grow by demand. `nursery-v2-extension.json` is
the obvious next candidate — one writer today, and nothing structural says so.
