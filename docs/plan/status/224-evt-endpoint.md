# Lane: evt-endpoint — EVT endpoint exclusion for x^3-6x on [-3,2], kernel-reconstructed as a sibling fact

<!-- plan-section: lane-status -->

**Your lane's block (`DONE this pass`, evt-endpoint, 2026-08-28).**

The previous lane (`223-cas-reconstruct`) sized this as needing no new kernel
machinery: `docs/plan/status/223-cas-reconstruct.md`'s "Next lane" item 1. That
sizing HELD, verified rather than trusted:

- `q = p - p(-3)` (coefficients `[9,-6,0,1]`), `r = p - p(2)`
  (`[4,-6,0,1]`) for `p = x^3-6x`. `q(-1) = 14`, `r(-1) = 9`, exactly the
  constants the previous lane's write-up sized.
- Both admitted through `crate::Kernel::add_declaration` using the EXISTING
  `zero_lt_via_nat_le` engine (`rat_prelude/cas_ivt_bridge_tests.rs`) — no new
  `rat_prelude` lemma, kernel primitive, or proof pattern.

`scripts/validate-facts.py`, `cas-certificate` split, before/after (this
worktree):

```
before: cas-certificate: 31 total -- kernel-reconstructed 3, cas-internal 28
after:  cas-certificate: 32 total -- kernel-reconstructed 4, cas-internal 28
```

**What was built.** `crates/axeyum-lean-kernel/src/rat_prelude/cas_evt_bridge_tests.rs`
(new file, wired via `#[cfg(test)] mod cas_evt_bridge_tests;` in
`rat_prelude.rs`), one test:
`rat_prelude::cas_evt_bridge_tests::tests::evt_endpoint_exclusion_kernel_checked`.
It:

Detail moved to [`../notes/224-evt-endpoint.md`](../notes/224-evt-endpoint.md).

<!-- plan-section: landed-changes -->

| 2026-08-28 | evt-endpoint | `cas-certificate` `kernel-reconstructed` 3 -> 4: EVT endpoint exclusion for x^3-6x on [-3,2] admitted through `Kernel::add_declaration`, reusing the IVT sign-bracket bridge's engine verbatim; mutation-verified; registered as `F:cas-evt-endpoint-exclusion-cubic-kernel-checked`, a sibling of `F:cas-extremum-irrational-argmax` |
