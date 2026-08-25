# Notes: 122-lemire-integration

Detail moved out of [`../status/122-lemire-integration.md`](../status/122-lemire-integration.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

Verified: 694 `axeyum-cas` tests (690 pass, 4 ignored, 48 of them gf2); clippy
clean under `-D warnings`; `cargo check --workspace --all-features` clean;
`validate-facts.py` 347 facts / 0 errors; each retained fact's own
`checker_command` runs a nonzero passing count; the four `certificate-spec`
guards each mutation-verified to kill exactly one test (`__pycache__` cleared
between mutants); the new pre-push caller-safety assertion shown to fire on a
HEAD move, a staged file, and an untracked leftover, and to stay quiet otherwise.

Not pushed. The research record is exported to
`../lemire-half-degree-irreducibles` (`f7181da`, 768 files) and every source tip
is pinned under `archive/*` in this repository.
