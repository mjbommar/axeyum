# Notes: 96-transcription-binding

Detail moved out of [`../status/96-transcription-binding.md`](../status/96-transcription-binding.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**Scope, stated so nobody over-reads it.** Linear atoms only, and only the
`lra.hyp._N` / `lra.int_hyp._N` routes. The SOS route's `Real.mul` monomials and
every other `axeyum.reconstruct.*` namespace are **declined, not skipped** — an
unrecognized query-derived axiom fails the run, so the uncovered routes are
visible rather than silently blessed. 11 instances are excluded for exactly
these reasons, each named in the manifest.

**Next.** (1) Monomial support would take the 10 QF_NRA SOS instances, which is
the only route in the swept corpus that renders arithmetic this checker cannot
read. (2) `axeyum.reconstruct.dio.*` (18 Diophantine instances) is the next
namespace by instance count. (3) The 14 `ArrayAxiom` and 5 `QfAbv` modules
render hypotheses that are not linear atoms at all and need a different binding
argument.
