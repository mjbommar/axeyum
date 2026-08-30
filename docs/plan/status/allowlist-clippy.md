# Lane: allowlist-clippy — trusted-substitution allowlist coverage + workspace clippy cleanup

<!-- plan-section: lane-status -->

**Task 1 `DONE` (2026-08-27), 0 of 15 facts closed — a measured negative
result, not a failure.** Brief: extend `trusted_substitution`/
`nat_order_substitution`'s allowlist to cover `Nat.mod_lt`/`eq_self` (doc
294's estimate of the remaining gap for doc 292's 15 `Nat.Coprime`
`TrustedDeclaration` declines) and re-run the real failing exports.

Measured, not estimated, via a standalone NDJSON decoder against doc 292's
own s5 exports plus the real `statement_goal_record` binary: doc 294's "two
names" estimate undercounts the real closure. The smallest representative
fact needs **15** additional theorem-kind names beyond existing coverage,
not 2 — 7 are generic `WellFounded.fix`/eager-fixpoint internals (a
different, larger construction class `nat_order_substitution`'s technique
doesn't cover), the rest are ordinary order lemmas needing a `Nat.beq`
primitive that module doesn't yet discover. `eq_self` independently needs
`propext`, which this kernel deliberately excludes (intuitionistic design,
`prelude.rs:61`) — architecturally permanent, not deferred engineering.

**Split of the 15**: 1 permanent (`Quot`, hard rule, unchanged from doc
294), 5 permanent (need `propext`), 9 deferred (need the WF-recursion
cascade — real, doable, substantial future engineering, not attempted here
per the brief's own stop condition). 0 closed. No changes made to any of
the four substitution modules — nothing was safely addable within a
reviewed scope. Guard mutation test reproduced doc 294's result exactly (3
tests red with the whole-stream `matches!` guard neutered; restored clean).
Full writeup: `docs/autogenesis/295-mod-lt-and-eq-self-cascades-are-not-a-two-name-extension.md`.

Detail moved to [`../notes/allowlist-clippy.md`](../notes/allowlist-clippy.md).

