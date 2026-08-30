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

Detail moved to [`../notes/217-supon-r6c.md`](../notes/217-supon-r6c.md).

<!-- plan-section: landed-changes -->

| 2026-08-28 | supon-r6c | `CReal.meshLevelCount_pow` landed: cherry-picked alone from the broken `worktree-agent-a8d6d5209f5a4bb3d` branch, then fixed a SECOND bug (missing `lam_fv` wrap on the induction value) beyond the symm-argument fix the brief credited; `creal_prelude_builds` green |
