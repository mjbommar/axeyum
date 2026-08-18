# Notes: 100-ledger-freshness

Detail moved out of [`../status/100-ledger-freshness.md`](../status/100-ledger-freshness.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**What re-measuring found that no number check can see.** The same evidence entry
described a facade emitting a 21-line structural shim; the facade has emitted a
real 62-line `Lra` module that carries ordered-field content since the dispatch
fix of 2026-08-15, and the strict front door now *accepts* where the prose says it
declines. That is a larger staleness than the count, it survived three re-reads,
and arithmetic gating is structurally blind to it. Recorded in the fact rather
than papered over.

**Next.** Two candidates, in order. (1) The same anchor for `depends_on` and
`checkers` counts, which needs a naming convention in `supports` before it can be
mechanical. (2) The class one level out: derived numbers in *doc comments* — the
example's own module doc also said 30 and was corrected here, and nothing gates
that at all.
