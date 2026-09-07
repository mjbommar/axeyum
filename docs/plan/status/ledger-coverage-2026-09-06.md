# Lane `ledger-coverage` — one coverage number, facts for four blind spots, and a reworded headline

<!-- plan-section: lane-status -->

**Status:** all four deliverables landed. Deliverable 3's optional gate is
deliberately NOT shipped, with the measurement showing why. ADR-1674.

## The headline numbers, re-measured rather than inherited

| | measured 2026-09-06 |
| --- | --- |
| kernel theorems (`prelude_theorem_inventory --include-constructed`, release) | **3,079** |
| registered by a fact | **2,358** |
| **not registered by any fact** | **721** |
| proved facts | 2,687 |
| with an empty `axiom_footprint` | **2,584** |
| non-empty | 103 |
| proved on `kernel-lean` | 2,586 |
| `kernel-lean` **with a non-empty footprint** | **2** |

Reproduce the first three with `python3 scripts/gen-ledger-coverage.py`, the
rest with `python3 scripts/validate-facts.py` (whose `routes:` line already
prints the honest form: `2584 axiom-free on kernel-lean (not comparable across
routes)`).

## What landed

| SHA | what |
| --- | --- |
| `f8d323bd0` | `--ratchet` over registered theorem NAMES + `artifacts/ledger-coverage-baseline.json`; stale artifact regenerated (2,539 → 3,079); `characterization`/`list` bucketing fixed; registered in `justfile` and `check.sh` |
| `340040c7e` | 17 mutation guards, 33 → 50 tests, and the merge of a `SUITES["ledger-coverage"]` suite that had never run |
| `cd94e5bb9` | the four unqualified axiom-free sentences outside `docs/math-department/`, reworded; 430 retired |
| `2de2ae731` | three CAS-capability fact rows at `computed` |
| `e2e17524f` | ADR-1674 and this file |
| `918752ac7` | regenerated `PLAN.md` |
| `fd2dbde8b` | the five geometry-certificate fact rows + four regenerated artifacts |

## Findings, in the order they matter

**1. `--check` was not a ratchet.** It compares the committed artifact against a
fresh generation, so it fails on staleness and nothing else. Regenerating
satisfies it however far coverage has fallen. `--ratchet` now ratchets over the
SET of registered theorem names, so a swap is caught too, and the population is
the INTERSECTION of the kernel inventory with the names facts claim — which is
what makes it un-gameable. Run, not argued: adding a fact naming a theorem the
kernel does not declare left `registered` at 2,358.

**2. The committed coverage artifact was stale by 540 theorems** (2,539 vs
3,079). Nothing was broken; nobody had regenerated it. This is why the ratchet
and the regeneration check are one invocation now.

**3. `430` does not reproduce.** Neither ADR-1605 nor `AUDIT-2026-09-04.md`
recorded the query. Retired at every use, with the reason recorded beside it
rather than the number silently swapped. ADR-1605's example survives:
`AlgS.Hom.firstIso` is still unregistered, as are 101 of the 151 theorems in
its `characterization` prelude.

**4. A mutation suite that had never run.** `scripts/tests/mutation_controls.py`
held two `SUITES["ledger-coverage"]` assignments 327 lines apart; the second
replaced the first, discarding seven guards. Merged; all seven now kill. The
additive-merge hazard one level up from source — "keep both sides" of a dict
assignment parses fine and discards one.

**5. `prelude_of` was misfiling 151 theorems.** The `characterization` and
`list` preludes post-date its namespace map, so `AlgS` (115), `CatS` (21),
`Alg` (15) and `List` (17) fell through to the `logic` catch-all, reporting
`logic` as 206 theorems for the 55 it owns. Invisible in the overall counts,
because the denominator is a set of names and does not care which bucket prints
it.

**6. The axiom-free headline was the wrong SHAPE, not just a stale count.**
Three of the six proof routes structurally cannot report an empty footprint —
`AXIOM_FREE_CAPABLE` is the one-element set `{kernel-lean}` and the validator
*fails* a `[]` on the other five. So a universal over the ledger has never been
available. Of the 103 non-empty facts: 60 `cas-certificate`, 17
`smt-term-level`, 10 `smt-clausal`, 7 `search-certificate`, 7
`imported-kernel-lean`, 2 `kernel-lean`. **Correction to the circulating
wording:** "the rest are CAS-internal residue labels" covers only 60 of the
101; the precise form is "101 are on routes that cannot claim it, and 2 are
named `kernel-lean` exceptions".

## For the owner of `docs/math-department/` — four sentences I did not edit

I was told not to edit that directory. These four are unqualified-false as
written; line numbers as of `29953abe1`.

| file:line | the sentence | note |
| --- | --- | --- |
| `README.md:104` | "Every proved row carries an axiom footprint read from `Kernel::axiom_footprint`, and the headline is that the footprint is empty." | contradicts **line 50 of the same file**, which already carries the corrected form |
| `12-the-chair.md:282` | "…empty footprint throughout…" | history row, 2026-09-04 |
| `12-the-chair.md:284` | "…every proved fact with an empty axiom footprint." | history row, 2026-09-06; row 285 corrects it but 284 is unamended |
| `10-logic-and-foundations.md:298` | "2,487 proved facts, empty footprint." | history row only; the file's body at 137–139 is already correct |

Also in that directory: the pasted audit blockquote quoting **430** appears in
all twelve reviewer files (`01`…`12`, at lines 16, 68, 19, 27, 16, 31, 18, 28,
23, 15, 16, 19). Only `10` and `12` carry the retraction inline. The primary
sources outside the directory are fixed; `AUDIT-2026-09-04.md:30,34` and
`00-roadmap.md:271` are not, being yours.

Suggested replacement wording is in ADR-1674 § "The headline says what it
measures". One warning: do **not** reach for "all `kernel-lean` facts are
axiom-free" as the safe qualified form — it is false by exactly two.

## The five geometry-certificate facts

`F:geometry-pascal-parabola-hexagon`, `F:geometry-desargues-affine-perspective`,
`F:geometry-conic-polar-is-tangent`, `F:geometry-tetrahedron-medians-concurrent`,
`F:geometry-tetrahedron-perpendicular-bisectors-concurrent` — all `proved` /
`cas-certificate` / no `cas_substance` block, matching their ten committed
siblings. Their SMT-LIB statements are RENDERED from the certificate JSON term
by term rather than transcribed, so every ratio
`check-geometry-fact-transcription.py` reports is exactly 1.

The two tetrahedron rows carry
`geometry.cartesian-coordinatisation-of-euclidean-3-space` and NOT the
plane-coordinatisation entry their ten plane siblings use; each says why in its
`notes`. Copying the plane entry would have been the easy wrong answer, and it
would have put a false assumption into the footprint of the only solid geometry
in the system.

Verified independently of the lane that wrote them, including a negative
control on a DIFFERENT fact than that lane mutated: changing one coefficient
`4.0` → `5.0` in `F-geometry-tetrahedron-medians-concurrent` takes the
transcription checker to exit 1 and it names the fact
(`conclusion[0] is not a constant multiple (3/2 then 61/41)`); restoring it
returns exit 0.

**Coverage is unmoved by all eight new facts, as it should be**: `registered`
stays 2,358 of 3,079, because these are `cas-certificate` rows and the
ratchet's population is `kernel-lean` theorem names. The only change to
`artifacts/ledger-coverage.json` is `facts_scanned` 2963 → 2971. Eight honest
facts must not move a kernel coverage number, and they did not.

## What did NOT land, with the measured obstruction

**A regex gate for the false wording — deliberately not shipped.** The brief
asked for one "if you can write one that cannot fire on a correct sentence".
You cannot, because **the retraction and the offence are the same string**: a
document corrects the claim by quoting it. Measured with the obvious gate
(universal quantifier + axiom term in a two-line window, excused by an adjacent
route name or count): 8 raw hits, 6 excused, 2 would fail — and it is wrong in
**both directions in one file**. It fails on `12-the-chair.md:121`, inside the
section that labels the claim measured false; and it excuses `12-the-chair.md:284`,
a genuinely false sentence, because that line contains `2,668` and "carries a
count" was the exculpating signal. A checker that passes the false sentence and
fails the correction is worse than no checker.

**All eight fact rows landed** — see the deliverable-2 section above and
`fd2dbde8b`. Nothing from deliverable 2 was dropped.

**Not attempted:** `fo_*`, `metric_prod` and list-prelude index coverage. The
denominator here includes those preludes exactly to the extent
`prelude_theorem_inventory --include-constructed` prints them (`list` appears,
at 17 theorems, 16 registered); lane `index-coverage` owns the index side.

## Gates run

| gate | result |
| --- | --- |
| `python3 -m unittest scripts.tests.test_gen_ledger_coverage` | **50 tests**, OK |
| `python3 -m scripts.tests.mutation_controls ledger-coverage` | baseline green at 50; **17/17 guards killed**, exit 0 |
| `python3 -m scripts.tests.mutation_controls --check-anchors` | `suites=101 anchors=935 stale=0`, exit 0 |
| `python3 scripts/gen-ledger-coverage.py --check --ratchet` | `baseline=2358 registered=2358 lost=0`, exit 0 |
| `python3 scripts/validate-facts.py` | 2,966 facts, **0 errors**, exit 0 |
| `python3 scripts/check-cas-substance.py` | 16 kernel-reconstructed, ratchet floor 14 held, exit 0 |
| `python3 scripts/gen-adr-index.py` | `rows=884`, exit 0 |
| `./scripts/check-links.sh` | all links ok, exit 0 |
| `cargo test -p axeyum-cas --lib enclosure::` | 62 passed |
| `cargo test -p axeyum-cas --lib enclosure_special::` | 30 passed |
| `cargo test -p axeyum-cas --lib enclosure_integral::` | 44 passed |
| `cargo test -p axeyum-cas --lib matgroup` | 61 passed (26 + 35) |
| `cargo test -p axeyum-cas --lib chartable::` | 28 passed |

## Reported, not fixed

`scripts/tests/mutation_controls.py` also holds three byte-identical
`SUITES["self-demo"]` assignments (sha `439d7513288b`, so nothing is lost) and
three top-level definitions each of `main`, `run_demo` and `check_anchors`.
Only the last of each runs. These belong to other checkers; a lane that owns
them should collapse them.
