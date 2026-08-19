# Lane: golden-pins — a header change can no longer move a proof pin

<!-- plan-section: lane-status -->

**The module banner is out of the golden pins, and the golden suites have a
gate** (`WIP`, agent-golden-pins, 2026-08-18). Three commits in four days
changed the fixed banner every rendered Lean module opens with, re-pinned only
the golden that sat in a gate, and shipped the same delta red onto the rest
(`0fc7cc357`; `b760fd6ae` +863; `46724faec` +777). Two things were wrong and
both are fixed:

1. **the pins covered the banner.** `axeyum_lean_kernel::split_module_banner`
   plus `tests/support/lean_golden.rs` pin the module **body**; the helper still
   refuses a source that does not open with this kernel's banner byte for byte.
   The banner has one pin of its own, as committed text
   (`axeyum-lean-kernel --test module_banner_pin`, blessed by the same
   `AXEYUM_BLESS_LEAN_FIXTURES=1` as the 17 module fixtures). A header change
   now fails one named thing and its failure is a header diff.
2. **nothing ran the suites.** `scripts/check-lean-golden-pins.sh` **discovers**
   membership (a suite is in the gate exactly when it calls
   `assert_golden_module`) and refuses a hand-rolled whole-module `(len, fnv1a)`
   pin, so a new golden cannot be added outside the gate. Wired into `just
   check` and `scripts/check.sh` (both, keeping `check-aggregate-scope` clean)
   and diff-scoped into `hooks/pre-push` on `axeyum-lean-kernel/src/**` — the
   origin of all three recurrences.

Membership measured, not guessed: **five** suites, the four that failed plus
`diophantine_lean_reconstruct`. The four candidates in the brief's regex are all
false positives (`specs.len() == 720`, `== 640`, corpus population `226`,
`outer_bindings.len() == 318`) — element counts, not module bytes. Detail and
the full measurement table: [`../notes/agent-golden-pins.md`](../notes/agent-golden-pins.md).

<!-- plan-section: landed-changes -->

| 2026-08-18 | (pending) | `lean_pp::split_module_banner` + `tests/support/lean_golden.rs`: golden pins cover the module BODY, banner pinned once as committed text in `module_banner_pin`. |
| 2026-08-18 | (pending) | `scripts/check-lean-golden-pins.sh` (+ controls): the golden-module gate, membership DISCOVERED not listed; wired into `just check`, `check.sh`, and diff-scoped `hooks/pre-push`. |
