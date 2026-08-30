# Notes: 130-ledger-integral

Detail moved out of [`../status/130-ledger-integral.md`](../status/130-ledger-integral.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

Every `checker_command` was written so its exit status depends on what the
run finds (`theorem_dependency_inventory` + anchored `grep -c`, never `-q`,
never `\t`), per this session's standing audit of vacuous checkers. Mutated
three theorem display names (`riemannSum_cauchy`, `integral_converges`,
`sharedIndexToCanonical`) in an isolated `/data0` snapshot
(`scripts/lane-snapshot.sh`, never the shared checkout) and confirmed each
corrupted name's own checker fails (grep count 0, exit 1) while unrelated
control names in the SAME rebuild still pass — see the fact files'
`notes` for the exact mechanism. `CReal.integral` itself is a `Definition`,
which no in-tree inventory tool names with fail-on-absence semantics (they
all filter to `Declaration::Theorem`), so its presence check is necessarily
indirect (via `integral_const`'s admission) and documented as such.
`python3 scripts/validate-facts.py` is green: 708 facts, 0 errors.

**Two mathematical facts recorded precisely, not just asserted:**
`CReal.integral_split` (interval additivity) stays unregistered — it is
neither proved nor refuted, only its FIXED-MESH `riemannSum` special case is
refuted (exact counterexample in `creal/integral.rs`'s module doc, cited in
`F:creal-riemannsum-integral-close`'s notes so a reader does not conflate the
two). `integral_witness_independent` is registered as its own fact rather
than folded into the construction, per the task briefing.

Nothing under `crates/` was touched — four lanes were live there
(`creal/integral.rs`, `creal/geometric.rs`, `creal/trig.rs`, `complex/`).
