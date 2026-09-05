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

**Scope, and why coverage moved 14 points rather than 141.** This lane
examined all **70** `docs/`-owned BARE candidate sites (the other ~72 of the
141 the census counted at start were under `crates/`, out of scope, or root
`CLAUDE.md`, also out of scope). Of those 70, **15 became markers and 55 were
rejected** as not genuine, checkable absence claims about *this kernel's own*
`kernel.environment()`. The single largest rejected class (~30 sites): prose
about autogenesis import/production *targets* ("the target support kernel",
"r082", "the selected closure", a specific capsule's dependency footprint) —
these use `Root.name`-shaped identifiers but the claim is about a one-off
import snapshot or dependency-closure measurement, never about the persistent
kernel this gate's authority builds. Marking one of those would either fail
the "unanswerable" check for the wrong reason or, worse, pass by coincidence
while asserting something this gate was never designed to check. The next
largest rejected class: candidates that are the SUBJECT of an existing
positive statement in the same paragraph ("confirmed present", "already
declares", "all landed") — the extractor pulls every `Root.name` in the block,
most of which are being cited as *evidence of presence*, not claimed absent.

**8 live `absent:` markers added** (all independently re-verified against the
fresh authority before marking):

- `docs/curriculum/foundational-books/spivak.md` — `Complex.exp`, `Complex.arg`
- `docs/curriculum/graded-statement-families.md` (two separate blocks) —
  `Complex.fundamentalTheoremOfAlgebra`, `Complex.exp`, `Complex.arg`
- `docs/plan/status/142-fta-assess.md` — same three
- `docs/reference/examples.md` — `Complex.le`, `Complex.lt` (permanently
  refuted by `Complex.no_compatible_order`, not merely unbuilt)
- `docs/research/09-decisions/adr-0611-an-absence-claim-in-prose-must-expire.md`
  — `CReal.within_of_close_within` (the ADR's own seed-5 discussion; the
  status doc above already carries the canonical live marker for this
  declaration, this is a second, independent live claim in a different
  document making the same assertion)
- `docs/research/11-design-review/2026-08-27-locatedness-and-the-measure-theoretic-lesson.md`
  — `CReal.sup`
- `docs/plan/notes/99-capability-assurance.md` — `Nat.div_add_mod`

**7 STALE claims found and corrected — the headline finding, not the coverage
number.** Each was written as a live "does not exist" / "is absent" claim and
is now false; each got a short historical-record note plus a `was-absent:`
marker so the record survives under the gate rather than being deleted:

| File | Declaration(s) | Now |
|---|---|---|
| `docs/formalized-math-2026-08/diary-formalized-collect.md:89` | `Nat.le_refl` | exists |
| `docs/mathematics-2026-08/diary-flywheel-2026-08-25.md:35` | `CReal.sqrt` | exists (landed 2026-08-23) |
| `docs/plan/status/133-ledger-uc.md:22` | `CReal.alternatingBracketUpper`, `CReal.alternatingLowerBound`, `CReal.alternatingUpperBound` | all exist |
| `docs/plan/status/133-ledger-uc.md:96-107` | `CReal.uniform_converges_add`, `Nat.even_or_odd`, + the three `alternating*` names above | all exist |
| `docs/plan/status/69-creal-lattice.md:17` | `Rat.abs` | exists |
| `docs/research/09-decisions/adr-0512-real-is-constructed-as-a-setoid-over-the-rationals.md:124` | `Rat.le`, `Rat.sub`, `Rat.abs` | all exist |
| `docs/research/09-decisions/adr-0519-the-real-lattice-is-defined-on-the-representation-and-is-one-lipschitz.md:127` | `Rat.abs` | exists |

`Rat.abs` alone was independently written as a live "still does not exist"
<!-- was-absent: Rat.abs -->
claim in **three separate documents** — none aware of the other two. None of
these were caught by any existing gate; `check-absence-claims.py` did not
exist to catch them until today, and none had a `was-absent:` marker before
this lane. No downstream lane is known to have been dispatched against any of
these seven specifically (unlike the `CReal.weierstrassMTest` /
`Rat.sumRange` incidents ADR-0611 documents), but the mechanism is identical.

**Spelling:** no normalized-only hits were needed for any of the 15 new
markers — every declaration named matched the kernel's exact spelling. Two
candidates from the design-review docs (`CReal.congrOfUniformlyContinuous`,
`CReal.equiv_of_le_le`) were checked as part of due diligence on ADR-0608's
own paragraph and are both EXACT PRESENT under their stated spelling, so that
block was correctly left BARE (not a genuine absence claim — it is an
example of a spelling mismatch *risk*, not a claim that either declaration is
missing).

**`crates/` docs carrying a stale or live absence claim, reported and NOT
edited (out of scope — three lanes are live in `axeyum-lean-kernel`):**

- `crates/axeyum-lean-kernel/src/creal/trig_fn.rs:63` — still literally true
  (`CReal.within_of_close_within` genuinely absent); already the subject of
  a live marker in `docs/plan/status/151-absence-expiry.md:74` and now also
  in `docs/research/09-decisions/adr-0611-...md`. No new finding here.
- No other `crates/` stale claim was found among the 70 examined sites —
  the two root-`CLAUDE.md` BARE sites (`:1519`, `:1675`) are prose *about*
  this gate and the retrieval problem, not fresh absence claims of their
  own; left untouched as out of scope (`CLAUDE.md` is not under `docs/`).

**Gate stayed green.** `python3 scripts/check-absence-claims.py` exits 0
after every edit in this lane (re-run after each file, not just at the end).
No marker added here reds the gate; every stale correction was verified
against the fresh authority BEFORE editing, never after.

<!-- plan-section: landed-changes -->

| 2026-08-27 | (pending commit) | Absence-claim marker coverage: 4/145 -> 18/147 checkable sites (70 `docs/`-owned BARE candidates examined by hand, 15 marked, 55 rejected as not genuine kernel-absence claims). 7 stale "does not exist" claims found and corrected to `was-absent:` with a historical-record note (`Nat.le_refl`, `CReal.sqrt`, `CReal.alternatingBracketUpper`/`alternatingLowerBound`/`alternatingUpperBound`, `CReal.uniform_converges_add`, `Nat.even_or_odd`, `Rat.abs` x3 independently across three documents, `Rat.le`, `Rat.sub`). 8 new live `absent:` markers on currently-true claims (`Complex.exp`/`arg`/`fundamentalTheoremOfAlgebra` x3 sites, `Complex.le`/`lt`, `CReal.within_of_close_within`, `CReal.sup`, `Nat.div_add_mod`). Gate green throughout; `crates/` findings reported, not edited. |
