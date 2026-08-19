# Lane: doc-formalized — the formalized-math strand, corrected against measurement

<!-- plan-section: lane-status -->

**The strand's headline claims were falsified in both directions and are now
corrected in place, not rewritten** (`WIP`, doc-formalized, 2026-08-19).

- **"Theorems the system proved without a human writing the proof: zero"** —
  false since 2026-08-18. Three facts are `kernel-term` / `checked` / empty
  footprint, and all three re-derive today (`check-autogenesis-fact-operation.py`
  exits 0 on each). Two are `Eq.refl` from a blind producer (2 of 138 rows); the
  third (`Nat.fib_add_two`) was built by a target-specific program and repaired
  by hand across two failed runs, so it fails the autogenesis programme's own
  autonomy bar. **C2 — solver refutation → library theorem — is still zero.**
- **The 149/day rate**: the counter reads **139, unchanged**, on 2026-08-19 —
  6.4/day over 5.16 days. But it counts one prelude and production moved off it
  (Int: 57 derived, axiom-free). **No tool measures this project's theorem rate.**
- **"Lean's own kernel accepted an axeyum development"** was true and narrower
  than it read — reachability-filtered, 343 of 465. ADR-0517/0518 now live in
  the strand: Lean's kernel takes all 470 carrier declarations, its elaborator
  refuses four, our kernel is **not** the permissive one, and any decline census
  must name which checker it ran.
- **C1 (shard `nat_prelude`) is DONE and did not deliver.** 845 lines in eleven
  modules, first splits 2026-08-14; five days of collision-free library produced
  +33 theorems. `N x 149/day` is falsified by its own remedy.
- Stale status blocks in `03`/`04` (13-of-40, population UNSTARTED, "import ℚ
  and ℝ", "`#print axioms` run by hand") left visible with what falsified them.

Measured, not cited: trusted surface `…/rat/string 0 · real 30`; front door
1,304,276 / 1,330,091 / 1,442,247 B, zero carrier axioms, `Real` control
non-vacuous; `check-lean-gate.sh` green at **21 suites, 66 tests, 473 checks**
(floor 219) — **40 of 77 crosscheck families are attestations**, now in `03`
because "473 modules read" is not "473 propositions proved".
Detail: [`../notes/107-doc-formalized.md`](../notes/107-doc-formalized.md).

<!-- plan-section: landed-changes -->

| 2026-08-19 | `PENDING` | `docs/formalized-math-2026-08/` corrected against measurement: "system-proved theorems = zero" falsified (3 facts, re-derived, heavily qualified; C2 still zero); C1 landed 2026-08-14 and did **not** deliver `N x 149/day`, so the single-file-lock diagnosis is falsified by its own remedy; the rate metric retired as unmeasurable across preludes; ADR-0517/0518's two-checker finding and the 122-declaration coverage hole recorded, with the limitation stated at its true width (shipped artefact does not carry the whole carrier; 4 declarations kernel- but not elaborator-checkable). |
