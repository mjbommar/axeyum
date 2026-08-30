# Notes: 217-supon-r6c

Detail moved out of [`../status/217-supon-r6c.md`](../status/217-supon-r6c.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

Job 2 (diagnose `hclose_of_uc`'s `UnboundFVar`): **the previous lane's
hypothesis (a leak inside one of ~15 `le_congr`/`rat_eq_rewrite`
composition steps in `hclose_of_uc` itself) is very likely WRONG, and
Job 1's fix is almost certainly Job 2's answer too.** `hclose_of_uc` is
not in this tree (never cherry-picked, out of scope per the brief) so
this is not independently re-confirmed against the real `hclose_of_uc`
code, but the evidence is strong: id 17535 is deterministic given the
same preceding `BuildStep` order, and it reproduces from
`meshLevelCount_pow` ALONE with no `hclose_of_uc` code present at all.
`hclose_of_uc` calls `d.lemma(p.mesh_level_count_pow, &[j])` — if
`meshLevelCount_pow`'s own `add_declaration` never actually succeeded in
that lane's session (their commit message says "not yet confirmed to
kernel-accept" for both), the full-prelude test would fail at
`meshLevelCount_pow`'s step, before `hclose_of_uc`'s step ever runs —
and `creal_prelude_builds_body` reports whichever step fails first
without naming it, so attributing the failure to `hclose_of_uc` was an
inference, not a measurement. The previous lane's `scan_fvars_local`
correctly found nothing in `hclose_of_uc`'s own `ty`/`value` because the
leak lives in a *different*, earlier declaration's stored value, not in
the term it scanned.

Recommendation for whoever picks up `hclose_of_uc` next: re-apply this
lane's `lam_fv` fix (already on this branch), then re-attempt
`hclose_of_uc` on top of current `main`. If `UnboundFVar` recurs with a
*different* id, the composition-step hypothesis becomes live again; if
it now succeeds or fails differently, this was the whole bug.

Performance (both personally measured, `env -u RUST_MIN_STACK`,
`scripts/cargo-serialized.sh test -p axeyum-lean-kernel --lib
creal::creal_tests::creal_prelude_builds`, test-reported time only):
- `main` (335da8ba5): 115.49s
- this branch (job 1 landed, both bugs fixed): 112.03s

No regression; the two are within normal host-contention noise.

Nothing found stale in `creal/supremum.rs`'s module doc during this
session — did not have cause to read it end to end (scope was two
narrow bug fixes, not the module's documented design).
