# Notes: 326-golden-lean-check

Detail moved out of [`../status/326-golden-lean-check.md`](../status/326-golden-lean-check.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

Doctored-module negative control, run manually per suite (not committed as a
permanent test — same as diophantine's own check has none): copied each
suite's already-written `.lean` module, flipped the theorem's stated type from
`theorem axeyum_refutation : False :=` to `... : True :=`, and re-ran the
pinned `lean` binary directly. All five (including diophantine, as the
existing-shape control) rejected with `exit 1` and a type-mismatch error
(`... but is expected to have type True`). So each new check can fail.

Also wired the four new suites into `scripts/check-lean-gate.sh`'s suite list
(next to `diophantine_lean_reconstruct`) and raised `CHECK_FLOOR` 219 -> 223 —
without this, a plain `cargo test` on these suites just prints
`AXEYUM-LEAN-SKIPPED` and passes when no Lean is found, which is the exact
"skip reads as a pass" failure this whole family exists to close.
`check-lean-gate.sh` is already registered in both `scripts/check.sh`
(`step lean-gate`) and the justfile's `check` recipe, so no further
registration was needed.

Did not run: `scripts/check-lean-gate.sh` itself (21 suites, well beyond the
task's scope — instructed to run only the five suites, `cargo fmt --all
--check`, and clippy on this crate), `just check` / `./scripts/check.sh`
(explicitly out of scope; the dispatching lane re-verifies before merging).
`bash scripts/check-merge-hygiene.sh` run at the end of this session — see its
output in the commit history / session report.

No pin constants were changed; `diophantine`'s existing test is untouched
except that it was re-run (unmodified) as a control.
