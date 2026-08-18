# Lane: transcription — the rendered statement must be what the file said

<!-- plan-section: lane-status -->

**The weakest link in the trust chain is now gated** (`WIP`, transcription,
2026-08-17).

`docs/prover-track/research/13-residual-trust-surface.md` ranks what a third
party must believe, and puts the SMT-LIB → rendered-statement transcription at
item 3, **weaker than the kernel**: a reconstructed UNSAT declares the query's
constraints as the Lean module's own axioms and proves `False` from them, and
nothing checked that those axioms are the `.smt2` file's `(assert …)` lines. A
dropped negation would typecheck, report a clean axiom footprint, and be
worthless.

Measured first, as the note said: **nothing checked it.** The closest existing
instruments count hypotheses (`hypotheses >= assertions.len()`) or test the
declared type for the substring `Real.le`. Neither reads what a hypothesis
*says*.

`scripts/check-lra-hypothesis-binding.py` closes it for the two arithmetic
hypothesis routes. Both sides are re-parsed and re-normalized in Python —
sharing no code with each other or with `axeyum-smtlib` — because the renderer
emits `x > 5` as `-x + 5 < 0` and normalization is exactly where the bug would
hide. Every rendered hypothesis must be an atom the query **entails**, under one
injective, sort-respecting renaming; every axiom in the module must be a
carrier, a bound hypothesis, or a pinned prelude law, so `axiom smuggled : False`
cannot pass unread. **105 instances, 248 hypotheses, 0 failures** (~30s), swept
from the committed corpora rather than hand-picked.

Two things it does that the count above does not convey:

- **It corrupts the real artifacts on every run.** Each hypothesis, five ways.
  869 caught. The gate cannot pass without its detector firing — this repository
  measured 40 of 162 checker runs exiting 0 on completion alone.
- **The search is untrusted.** Its 329 *accepts* of corrupted modules are not
  misses: `x ≤ 0` shifted to `x ≤ 1` names a different genuine row, and swapping
  the sides of `x − y < 0` is faithful again under the renaming that swaps `x`
  and `y` (measured, on a real cvc5 regression file). Each accept is re-derived
  by `verify_binding`, which shares no control flow with the search. A pristine
  accept the binding cannot justify fails the run too.

Writing it found a defect in the checker's own search — it committed to the first
permutation inside a matched atom and reported a transcription defect on a
**faithful** module (`x+y=1 ∧ x=2 ∧ y=0`). Pinned as a regression.

Detail moved to [`../notes/96-transcription-binding.md`](../notes/96-transcription-binding.md).

<!-- plan-section: landed-changes -->

| 2026-08-17 | `pending` | transcription: bind every rendered Lean hypothesis back to the query text — 105 instances, 248 hypotheses, 869 corruptions caught per run |
