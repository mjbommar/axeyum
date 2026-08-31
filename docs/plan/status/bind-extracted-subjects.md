# Lane: bind-extracted-subjects — verify and bind `formal.kernel_theorem` for extraction-resolved facts

<!-- plan-section: lane-status -->

**Done (bind-extracted-subjects, 2026-08-31).** ADR-1000's five-risk audit
measured that `theorem_of` (`scripts/check-fact-depends-derived.py`) resolves
1,320 settled facts authoritatively via `formal.kernel_theorem`, 664 by
extracting the first dotted name out of a `checker_command`, and 185 to
nothing — and that the extraction tier is documented as unreliable, with two
named failures. This lane re-measured, verified each extracted subject
against the live kernel (never by trusting the extraction), bound the ones it
could confirm, and reported the ones it could not.

**Measurement (this tree, 2026-08-31).** Over ALL 2,169 settled facts (any
`proof_route`), `theorem_of` resolves 1,320 authoritative / 664 extracted /
185 none — an exact match to the audit's numbers; nothing moved. Restricted
to `proof_route == kernel-lean` (2,087 settled, the population both
`check-fact-depends-derived.py` and `check-trust-closure.py` actually
enforce): 1,306 authoritative / 660 extracted / 121 none. The other 4
extracted facts are `proof_route == imported-kernel-lean` (`Bool.and_comm`,
`List.nil_append`, `Nat.le_refl`, `Nat.le_succ`) — real Mathlib/Lean4export
names, not axeyum-lean-kernel declarations, so `kernel_declaration_projection`
cannot verify them and neither gate consults them. Left untouched, out of
scope.

**Verification method.** Built `kernel_declaration_projection` once (2,542
declarations: name, kind, canonical rendered type) and cross-checked all 660
kernel-lean extracted subjects two ways: (1) exact string match of the
projected canonical type against `formal.statement`/`kernel_statement`
(catches a wrong name outright — 449 facts); (2) for facts without an
embeddable rendered type (mostly `lean4-surface` mirrors), confirming the
extracted name is the ONLY thing an anchored grep/awk filter in the fact's own
`checker_command` could have matched (not merely present as a substring
inside a larger embedded type — that distinction is exactly what made the
cassini extraction fail) — 209 facts. Total 658 verified-correct, 2
verified-WRONG (see findings). Every one of the 658 also exists as a
`Declaration::Theorem` in the projection, never a `Definition`/`Axiom`/other
kind.

**Findings — extraction was wrong, not merely unaudited:**

1. `F:nat-bitwise-bit` extracted `Nat.bitwise_bit` — no such declaration.
   `evidence[].kernel_declaration` already independently named the real
   subject, `Nat.bitwise_bit'` (primed; the extraction regex excludes
   apostrophes on purpose, so it can never find a primed name). Its rendered
   type matches `formal.statement` byte-for-byte. Bound to the corrected
   name.
2. `F:farkas-refutation-over-constructed-reals` extracted `CReal.Equiv` —
   that's a real declaration, but a `Definition`, not a theorem, and not what
   the fact is about. Reading the fact: it measures a whole reconstruction
   pipeline across 5 fixtures (a package-level result), matching exactly the
   documented deliberate-`null` case. Bound `formal.kernel_theorem: null`.

No other wrong extractions found among the 660. 10 extracted names collided
across 2 facts each (up from the audit's 6/12 — the ledger moved); all 10 are
a native fact paired with its `ml430-*` mirror fact naming the same kernel
theorem, which is the intended shape (a mirror fact asserts the mirrored
Mathlib statement corresponds to that theorem), not contamination.

**Bound:** 660 facts total — 658 to the verified-correct name, 1 to the
corrected name, 1 to the deliberate `null`. Diffs are minimal: one field
inserted into `formal`, byte-verified against `git show HEAD:<path>` to touch
nothing else (script-verified, not spot-checked). 0 left in "extracted but
undeterminable" for the kernel-lean population — every one either confirmed
or refuted.

**Guards that started rejecting after a correct binding — reported, not
repaired (out of this lane's declared scope: `artifacts/facts/`
`formal.kernel_theorem` only):**

- `validate-facts.py` (`scripts/check-fact-depends-derived.py`): now exits 1.
  Before, `F:nat-bitwise-bit` resolved to nothing (extracted name absent from
  the theorem graph) and was silently excluded from this guard's enforced
  set. Now that it resolves to its real theorem, the guard can see its actual
  dependency closure and finds 4 real, previously-invisible missing
  `depends_on` edges: `Nat.le_add_right`, `Nat.le_trans`, `Nat.one_mul`,
  `Nat.succ_mul` (→ `F:nat-le-add-right`, `F:nat-le-trans`, `F:nat-one-mul`,
  `F:nat-succ-mul`). This is the guard finding a real gap it was blind to,
  not a regression from this lane's edit.
- `check-trust-closure.py`: now exits 1. `guard_population`'s
  `COVERAGE-BELOW-FLOOR`: resolved-subject ratio dropped from 0.9583 (at the
  pinned floor) to 0.9578. Mechanism: before this lane's fix,
  `F:farkas-refutation-over-constructed-reals` was silently counted as
  RESOLVED against `CReal.Equiv` (a Definition — `collect_subjects` doesn't
  filter by kind) and fed into the self/alias/forbidden-trust closure guards
  under a subject that was never its real one. Correctly marking it `null`
  removes it from the resolved population, which is exactly what should
  happen — and reveals the recorded floor (`artifacts/trust-closure/population.json`,
  `min_ratio: 0.9583`) was resting on that one wrong resolution. Measured
  before/after with `--projection` pinned to the same environment snapshot so
  only the fact edits vary: before, `subjects=2000 unresolved=87` all guards
  clean; after, `subjects=1999 unresolved=88`, `population: hits=1`, the
  other three guards unchanged (0 hits both times).
- `check-settled-fact-statements.py`: now exits 1. `max_header_exempt`
  (a ratchet that only auto-tightens via `--write`'s `min()`) is pinned at 30;
  binding kernel_theorem onto 37 additional bare-type `lean4` facts (no
  `theorem NAME :` header — the same legitimate shape as the 30 pre-existing
  exemptions, e.g. `F:cassini-identity-over-constructed-integers`) pushed the
  count to 67. `--write` cannot loosen this automatically by design; a
  maintainer needs to review and deliberately raise the floor.

**Holdout isolation:** `scripts/check-autogenesis-holdout-isolation.py` —
PASS both before and after (`held_out=146, verdict=PASS`); `artifacts/autogenesis/`
carries 0 changes (`git status --porcelain` empty for that path throughout).

**Honesty on the unverified 4:** the 4 imported-kernel-lean extracted facts
are real names in a different formal system (Lean4export-imported Mathlib
terms) that this lane's tooling (`kernel_declaration_projection`, built from
`axeyum-lean-kernel`'s own preludes) cannot check at all — not "probably
fine," genuinely outside what could be verified here. Left unbound.

**Visibility note:** ADR-1000 and the five-risk audit doc this brief cites
were not present in this worktree (branched from `origin/main`; pushes lag).
Proceeded from the brief's own numbers, which this lane's independent
re-measurement reproduced exactly.

<!-- plan-section: landed-changes -->

| 2026-08-31 | bind-extracted-subjects | 660 facts in `artifacts/facts/` gained `formal.kernel_theorem` (658 verified-correct, 1 corrected, 1 deliberate `null`); ADR-1005 records the method and the 3 guards it caused to newly (and correctly) reject |
