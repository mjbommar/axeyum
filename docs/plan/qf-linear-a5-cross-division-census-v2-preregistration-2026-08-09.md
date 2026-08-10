# QF linear A5 cross-division census v2 preregistration — 2026-08-09

## Decision boundary

V2 supersedes only the process topology of the
[v1 preregistration](qf-linear-a5-cross-division-census-v1-preregistration-2026-08-07.md).
All frozen paths, list and historical-sidecar digests, row counts, semantic
validators, monotonicity controls, classification vocabulary, grouping rules,
outputs, and post-census authorization gates remain unchanged.

V1 failed closed when QF_RDL emitted 196/200 records and the shared address
space exited 101 under its 8 GiB cap. The row and last 21 rows pass in smaller
processes; `/proc` sampling showed allocator arenas retained across independent
files. [ADR-0379](../research/09-decisions/adr-0379-sequential-isolated-corpus-workers.md)
records the diagnosis and topology decision. V1's valid QF_LRA and QF_IDL
captures prove prior repairs but are not combinable with V2.

## V2 capture topology

For each division, the release `explain_corpus` invocation remains the sole
ordered stream owner and capture lane. It must:

- validate the complete frozen list before starting workers;
- run exactly one benchmark child at a time, in list order, using the same
  executable and shipped solver configuration;
- inherit the 8 GiB per-process `RLIMIT_AS` into every child, while making no
  aggregate cgroup-memory claim;
- retain the unchanged 24,000 ms query timeout and 6,000-second complete-stream
  outer timeout;
- accept exactly one identity-matching JSON record and zero stderr per child;
- stop nonzero on a child exit, stderr, empty/malformed/multiple output, or
  identity/order drift; and
- record topology `sequential-isolated-per-file-v1`, active-worker limit 1,
  memory scope `inherited-per-process-address-space`, and no aggregate-memory
  enforcement in each `axeyum-qf-linear-a5-capture-v2` metadata file.

## Restart and acceptance

After the implementation and ADR are committed, pushed, and fully gated, V2
restarts QF_LRA from row 1, then QF_IDL, then QF_RDL under the existing host
load and lock rules. Any behavior change or invalid stream restarts the whole
sequence again. No V1 row, partial RDL stream, diagnostic run, or timing result
is credited toward V2.

Only three valid atomic 200-row captures authorize the unchanged lossless
derivation. There is still no authorization to change solver routes, timeout,
resource ceilings, DL budgets, or score policy before that derivation.
