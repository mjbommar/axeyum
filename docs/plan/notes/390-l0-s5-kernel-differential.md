# Notes: 390-l0-s5-kernel-differential

Detail moved out of [`../status/390-l0-s5-kernel-differential.md`](../status/390-l0-s5-kernel-differential.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**Known open item, not closed by this slice:** the `inductives` mutant
(disabling the non-positive-occurrence check) SURVIVED unexplained -- the
targeted negative case did not flip, and the true rejecting mechanism was
not identified in the time available. `literals` and `quotient` also
survived their mutants, but for NAMED reasons (no case in this corpus
presents a malformed Nat bootstrap or a second quotient package) rather
than a mystery. The next lane on this phase should either root-cause the
`inductives` survival or explicitly reclassify it as an explained gap.

**What this does NOT cover** (stated in the test file's own doc comment,
repeated in ADR-0780): 4 cases per subsystem is not exhaustive. Missing:
mutual/nested inductive families, indexed families beyond 0-index, `Prop`-
restricted large elimination, structure eta beyond plain projection, string
literals, zeta reduction, well-founded recursion, longer reduction chains,
and malformed-package/malformed-bootstrap shapes for quotient/literals
specifically (exactly the gap the two "explained" survivals trace to).
