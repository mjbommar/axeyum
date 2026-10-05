# Lane: supon-r6c — salvage meshLevelCount_pow, diagnose hclose_of_uc's UnboundFVar

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, supon-r6c, 2026-08-28).**

Job 1 (salvage `CReal.meshLevelCount_pow`): **landed, and the prelude
builds green** — but the brief's premise that it was already
kernel-accepted was wrong. Cherry-picking `3c60b3208` alone (without the
symm-argument-order fix that actually lived in the *next* commit,
`ce5b0c29e`) reproduced the original `TypeMismatch`. Applying just that
one-line fix still failed, with `UnboundFVar { id: 17535 }` — the exact
id the previous lane attributed to `hclose_of_uc`. Root cause: in
`declare_mesh_level_count_pow_thm` (`creal/supremum.rs`), the `value`
returned by `d.induct(&motive, &base, &step, j)` was never re-wrapped
with `d.lam_fv(j_fv, nat, value)` to abstract the outer induction target
`j` into a real binder — compare `alternating.rs:383-385`, which does
`let value = d.induct(...); ...; let value = d.lam_fv(k_fv, nat, value);`
for the identical shape. Without that wrap, `ty` is a `Pi` but `value` is
a bare application containing a free `FVar(j_fv)` — an ill-formed pair
that only the kernel's own checker (not `cargo check`) catches. Adding
the missing `lam_fv` wrap fixed it; `creal_prelude_builds` now passes.

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

<!-- plan-section: landed-changes -->

| 2026-08-28 | supon-r6c | `CReal.meshLevelCount_pow` landed: cherry-picked alone from the broken `worktree-agent-a8d6d5209f5a4bb3d` branch, then fixed a SECOND bug (missing `lam_fv` wrap on the induction value) beyond the symm-argument fix the brief credited; `creal_prelude_builds` green |
