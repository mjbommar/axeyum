# Lane: ledger-freshness — a derived number written into prose goes stale silently

<!-- plan-section: lane-status -->

**The prose half of the ledger is now derived, not transcribed** (`WIP`,
ledger-freshness, 2026-08-18). `F:schedule-critical-chain-infeasible` said "the
30 axioms the kernel module actually rests on" for three days after its
`axiom_footprint` was corrected to 26 — with a correct `--expect-axioms 26`
sitting in the same JSON object. `depends_on` and the footprint array are both
derived and gated; the sentences *about* them were not, and nothing in the ledger
linked a number in English back to the thing it came from.

`scripts/check-fact-derived-numbers.py` closes that for one quantity, and only
one. It anchors **structurally**, not lexically: an `evidence[i].supports`
beginning with the literal field name `axiom_footprint` (the ledger's existing
convention, 48 slots), plus `--expect-axioms N` inside a command. Measured
2026-08-18 it binds **52 claims across 48 slots, 1 unchecked, out of 3,243
numeric tokens in fact prose** — and the docstring names the 3,191 it cannot see.
That gap is deliberate: 3 of the 7 phrases matching a naive `N axioms` regex are
about Peano's axioms, Armstrong's axioms, and a *different* theorem's footprint,
so a lexical gate over all of them would be 43% wrong and worse than none.

Seven guards, each with a fixture that trips it and no other; `mutation_controls.py
fact-derived-numbers` deletes each in turn and **every deletion killed exactly one
test**. Exit status was demonstrated on a scratch fact carrying the original stale
wording: exit 1 with three FAIL lines naming field and both numbers, exit 0 either
side of it.

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

<!-- plan-section: landed-changes -->

| 2026-08-18 | `4b5613e26` | `check-fact-derived-numbers.py`: every number a fact asserts about its own `axiom_footprint` re-derived from the array. Fixes `F:schedule-critical-chain-infeasible` (prose 30 vs array 26, plus an obsolete facade paragraph found by re-measuring: `Lra`/62 lines, not a 21-line shim) and the example's stale module doc. 52 of 3,243 prose numbers bound, denominator printed every run; 7 guards, each deletion kills exactly 1 test; wired into both `just check` (`facts`) and `check.sh` so `check-aggregate-scope.sh` records no new divergence. |
