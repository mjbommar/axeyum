# nursery-refill-draw-11 — status

Status: IN PROGRESS (started fresh after a server-error restart; branch
`nursery-refill-draw-11` off `origin/main` at merge-base, worktree
`/data0/axeyum/lanes/nursery-refill-draw-11`).

## Verified so far

- ADR-0910 (`Nat.nthRoot`, `Squarefree`, construction-only) is landed on
  this tree: `crates/axeyum-lean-kernel/src/nat_prelude/{nth_root,squarefree}.rs`
  both present.
- ADR-0900 (draw 10 declined) is cited in the brief but is **not** present
  in this worktree or `origin/main` (`docs/research/09-decisions/` tops out
  at ADR-0915 as of this lane's fetch) -- consistent with ADR-0910's own
  note that the same citation didn't exist on its tree either. Proceeding
  from ADR-0762 / ADR-0830 / ADR-0910 directly, which are in-tree.
- ADR-0910 explicitly left the environment snapshot regeneration to "the
  next lane" -- doing that now, before any select()/guard() screening,
  since the admissible() check reads `Nat.nthRoot`/`Squarefree` presence
  from `artifacts/autogenesis/kernel-environment-snapshot-v1.json`, not
  from the source tree.

## Next steps

1. Regenerate `kernel-environment-snapshot-v1.json` via `shape_search`
   (release build) + `gen-autogenesis-nursery-refill.py --snapshot-from`.
2. Re-run `select()`/`guard()` in memory (not writing FAMILY_MODULES yet)
   to confirm the 2-family lawful set still holds on THIS tree.
3. Weigh the two ADR-0910/note-383 caveats (closed-eval spend on
   `nthRoot_zero_left`/`nthRoot_one_right`; whether
   `Nat.nthRoot.lt_pow_go_succ_aux` is a fair blind target) before drawing.
4. Author the draw in `FAMILY_MODULES`/`FAMILY_ROUTES`, regenerate, verify
   the four required gates.

(Report will be filled in on completion.)
