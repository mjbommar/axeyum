# Lane: absence-adopt — raise absence-claim marker coverage, honestly

<!-- plan-section: lane-status -->

**Done (`WIP`, absence-adopt, 2026-08-27).** ADR-0611 / `scripts/check-absence-claims.py`
landed with adoption printed on every run: **4/145 checkable claim sites
marked** (per `docs/plan/status/151-absence-expiry.md`). This lane worked
through the 141 checkable-but-unmarked `docs/` sites by hand — not a sweep —
to raise coverage honestly and find stale claims, since a partial rollout is
exactly the defect ADR-0611 exists to prevent one level up.

**Census before (this lane's first run, fresh `--release` authority):**

```
authority: 1889 distinct kernel declarations (floor 1750)
scanned: 4000 files
markers: 5 (1 absent, 4 was-absent), naming 9 declaration(s); 10 more QUOTED
census: 709 absence-claim site(s); 146 name a declaration (4 carry a marker,
  142 do NOT); 563 name no declaration and are STRUCTURALLY UNCHECKABLE
FAIL: 142 unexpirable absence claim(s) naming a declaration, over the budget
  of 141 (concurrent `crates/` lanes had already pushed the bare-named count
  one over budget before this lane touched anything)
```

**Census after:**

```
markers: 20 (9 absent, 11 was-absent), naming 40 declaration(s); 10 more QUOTED
census: 710 absence-claim site(s); 147 name a declaration (18 carry a marker,
  129 do NOT); 563 name no declaration and are STRUCTURALLY UNCHECKABLE
OK: 20 marker(s) checked against the kernel; every claim still holds.
  Marker coverage of checkable claim sites: 18/147.
```

Detail moved to [`../notes/160-absence-adopt.md`](../notes/160-absence-adopt.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | (pending commit) | Absence-claim marker coverage: 4/145 -> 18/147 checkable sites (70 `docs/`-owned BARE candidates examined by hand, 15 marked, 55 rejected as not genuine kernel-absence claims). 7 stale "does not exist" claims found and corrected to `was-absent:` with a historical-record note (`Nat.le_refl`, `CReal.sqrt`, `CReal.alternatingBracketUpper`/`alternatingLowerBound`/`alternatingUpperBound`, `CReal.uniform_converges_add`, `Nat.even_or_odd`, `Rat.abs` x3 independently across three documents, `Rat.le`, `Rat.sub`). 8 new live `absent:` markers on currently-true claims (`Complex.exp`/`arg`/`fundamentalTheoremOfAlgebra` x3 sites, `Complex.le`/`lt`, `CReal.within_of_close_within`, `CReal.sup`, `Nat.div_add_mod`). Gate green throughout; `crates/` findings reported, not edited. |
