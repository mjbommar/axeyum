# Lane: nursery-draw-19b — draw 19 refused again, on a measurement this time: one viable held-out family and R5 needs two

<!-- plan-section: lane-status -->

**Done (`DONE — draw REFUSED`, nursery-draw-19b, 2026-09-02).** Draw 19 was
**not authored**. No family was added to `FAMILY_MODULES`, no manifest row was
written, no partition assigned, no held-out outcome named, nothing dispatched.
`artifacts/autogenesis/nursery-v1.json` and `nursery-v2-extension.json` are
byte-identical to their state at lane start (500 entries in the extension).
Decision: [ADR-1556](../../research/09-decisions/adr-1556-draw-19-is-refused-one-viable-held-out-family-and-r5-needs-two.md).

**The rule this draw applied, and why it is not the standing one.** The standing
rule was "no draw on a red partition gate". ADR-1551 established that the two
component gates' property cannot be restored by re-partitioning — `depends_on`
is proof-derived, so partitioning on it makes a row's partition a function of
whether we proved it — so waiting for those two to go green is waiting forever.
The rule applied here instead: **every gate that measures something a draw can
CONTAMINATE had to be green, and the two component gates are reported before and
after and must not worsen.** A fresh row carries `depends_on: []`, which is
exactly what those two gates read, so a draw cannot move them; both their
outputs are byte-identical before and after this lane.

## Gates, before and after (each run bare, exit captured before any `grep`)

| gate | before | after | headline (after) |
| --- | ---: | ---: | --- |
| `gen-autogenesis-nursery-refill.py --check` | 0 | 0 | `entries=500 development=180 held-out=190 train=130 env=2838 screen_drift=31` |
| `check-autogenesis-holdout-isolation.py` | 0 | 0 | `held_out=206 files_scanned=1114 references=0 PASS` |
| `check-holdout-adjacency.py` | 0 | 0 | 20 held-out families, 0 refused, 4 undisclosed (advisory) |
| `check-draw7-frozen-families.py` | 0 | 0 | `frozen=50 moved=0 new=0 control=FIRES PASS` |
| `check-partition-edges.py --baseline` | 0 | 0 | `drawn=716 crossing=198 baselined=198 violations=0 PASS` |
| `validate-facts.py` | 0 | 0 | 2611 facts, 0 errors |
| `check-autogenesis-nursery.py` | **1** | **1** | output **byte-identical**; 3 violation types, crossing components of 10, 4 and **305** |
| `check-development-partition.py` | **1** | **1** | output **byte-identical**; 1 violation, `open train=6 development=16 held-out=16` |
| `check-dispatchable-frontier.py` | **1** | **1** | G7, **2** dispatchable against a floor of 10 |

Every contamination-measuring gate was green at start, so the STOP condition did
not fire. The two component gates did not worsen — they did not move at all.

## Why the draw is refused: exhaustive, against the real screens

`docs/research/09-decisions/adr-1556-draw-19-screen.py` (loads the generator and
the adjacency checker by path; runs the actual `admissible()` /
`blockers_for()` / `screen_family()` / `barred_modules()` /
`is_closed_evaluation`; `propose-nursery-refill.py` is deliberately NOT the
candidate space):

```
ADR_1556_DRAW_19_SCREEN|env=2838|unowned_modules=23|unowned_rows=79
                       |distinct_tens=40668|viable=3|disjoint_pairs=0|failures=0
```

23 unowned modules still carry a screened candidate, **79 rows, 22 of them
`Mathlib.Data.Nat.Count`** (barred for held-out by ADR-1450). 861,809 module
subsets reach the ten-row floor; they produce **40,668 distinct drawn tens**;
**4 survive every held-out screen (3 after this lane's own refusal row)**. All
of them draw from the same four modules — `Mathlib.Data.Nat.Factorization.Basic`
(5 rows), `Mathlib.Tactic.IntervalCases` (2), `Mathlib.NumberTheory.PythagoreanTriples`
(1), `Mathlib.NumberTheory.SumTwoSquares` (1) — differing only in the tenth row.
A module belongs to exactly one family, so **at most one held-out family can
exist at a time and R5 demands two: 0 disjoint pairs.**

This reproduces **ADR-1420**'s finding for draw 17 on a tree four families
later; the blocking core has grown from one module (`IntervalCases`) to four.
Over the 19 modules disjoint from that core (70 rows, 11,030 distinct tens),
**zero** are viable; the 15 that fail on `barred` ALONE are all `Nat.Count`.

**Two corrections to the obvious method, both measured.** (1) Deduping by
MINIMAL MODULE COVER is wrong — a superset does not draw the same ten, because
an added module's names can sort earlier. Both passes are run (11,386
minimal-cover tens vs 40,668 exact) and the screen asserts they agree; here they
do. (2) The first control CLONED the blocking modules into independent copies
and **did not fire**: a clone carries the same row names, the dedup key IS the
drawn ten, so the clone's ten collapses onto the original's and no pair can
appear. It printed 418 viable tens and 0 pairs, which reads exactly like the
real finding. The working control lifts ADR-1450's `Nat.Count` bar and takes the
search from 3 viable / 0 pairs to **35 viable / 20 disjoint pairs**.

## The blindness screen draw 17 lacked

`shape_search` rebuilt through `scripts/cargo-serialized.sh`; freshness
confirmed against a control that landed the same day —
`--name Rat.rowEchelon --kind definition --expect 1` returns `FOUND 1`
(`Rat.rowEchelon` declared at 10:50 by `cd8d1f4a7`). Index 2,121 declarations.
All 13 distinct candidate rows screened by statement SHAPE plus
`git log -S --diff-merges=first-parent` (a plain pickaxe skips merge commits).

**One row is not blind, and only a shape query could find it:
`Int.gcd_eq_natAbs` (`a.gcd b = a.natAbs.gcd b.natAbs`) is `rfl` in this
kernel.** `int_prelude/gcd.rs:declare_gcd` builds `Int.gcd`'s VALUE as
`NatOps::gcd(d, natAbs a, natAbs b)` — the Mathlib statement, term for term, as
the definition rather than as a theorem — and three in-tree proofs already
discharge steps "by `Int.gcd`'s own definition". R9 is clean because the names
differ; R11's vocabulary map is clean because it holds only nursery family
subjects, never kernel development; the live environment sweep is EMPTY. This is
the ADR-1450 `Nat.count`/`Nat.countRange` shape on a new row. A
`do-not-draw-held-out` row for `Mathlib.Algebra.GCDMonoid.Nat` is now recorded
in `holdout-adjacency-review-v1.json` where `assert_draw_lawful` reads it, and it
BINDS: viable tens go 4 → 3 with it, and the `Int.gcd_eq_natAbs` ten is the one
that disappears.

**Three queries came back UNANSWERABLE (exit 3), not absent**, and re-asking
them in the kernel's own vocabulary is what made the screen honest: this kernel
declares no `Nat.Prime`, `Nat.Coprime`, `Nat.ModEq` or `Ne` — primality is
spelled as an `And`, coprimality as `Nat.gcd a b = 1`, congruence as
`Nat.modEq`. Re-asked, every other row is absent by shape with a live positive
<!-- absent: Nat.exists_eq_two_pow_mul_odd -->
<!-- was-absent: Nat.ModEq -- spelling-normalizes to the kernel's lowercase `Nat.modEq`, cited two lines above as the existing spelling; not a landing event, a naming-convention mismatch -->
control, including Euler's theorem (`Nat.ModEq.pow_totient`: absent, and the 19
`Nat.totient` theorems are multiplicativity/parity/divisibility, none a
congruence) and `Nat.exists_eq_two_pow_mul_odd` (absent; the nearest,
`Nat.dvd_two_pow_classify`, is a different proposition). No commit introduces
any of the 13 Mathlib names into `crates/`.

## The finding that outlasts the refusal

**A do-not-draw-held-out judgement about two of the four blocking modules is
enforced by nothing.** `gen-autogenesis-nursery-refill.py`'s draw-10 block
records that `Mathlib.NumberTheory.{SumTwoSquares,PythagoreanTriples}` were
"deliberately NOT taken" for held-out because `Int.sq_ne_two_mod_four` is mod-4
arithmetic adjacent to a published congruence family; ADR-0645 and
`325-nursery-draw.md` restate it. It is not a row in
`holdout-adjacency-review-v1.json`, so `barred_modules` cannot reach it — the
ADR-1450 shape again — and both modules are in **every** viable held-out ten
today. This lane did **not** convert it into a bar: the generator's wording is a
preference ("not worth a mild leak"), not a finding of non-blindness, and
promoting one lane's judgement into an enforced invariant is a separate
decision. The next lane should own it, because those two modules are load-bearing
for the only held-out family the pool can build.

## What unblocks draw 19

ADR-1420 Route 1, the same route draw 18 used: **a construction lane declaring
one held-out-safe module disjoint from `{Factorization.Basic,
PythagoreanTriples, SumTwoSquares, IntervalCases}`**, topic-, vocabulary- and
R9-clean. Overturning the `Nat.Count` bar is the only other lever the
measurement finds and it is not available — ADR-1450 measured four of its drawn
ten as already proved here term-for-term.

## Census and dispatchable, before and after

`frontier-shape-census.py`: **targetable 4 before, 4 after**, output
byte-identical (primary population 24, of which 11 mutation controls and 9
divergence-blocked). `check-dispatchable-frontier.py`: **2 before, 2 after**.
Both are unchanged because no row was drawn, which is the honest reading of a
refused draw and not a null result: the census's "largest coarse bucket holds 1
targetable fact" finding stands untouched.

## Did not run

`cargo test` / `cargo clippy` / `just check` / `scripts/check.sh` — no `.rs`
file was touched; the only `cargo` invocation was
`scripts/cargo-serialized.sh build --release -p axeyum-lean-kernel --example
shape_search`, needed for the blindness screen. `propose-nursery-refill.py`
without `--remeasure` was refused as an R2 stale snapshot and its ready-family
list at lane start (`Mathlib.Data.Nat.Log`, `Mathlib.NumberTheory.FactorisationProperties`)
described a tree draw 18 had already consumed; `--remeasure` was run and
`artifacts/autogenesis/refill-headroom-v1.json` regenerated by its own sole
producer.

<!-- plan-section: landed-changes -->

| 2026-09-02 | nursery-draw-19b | draw 19 REFUSED on measurement, not on a red gate: 40,668 distinct drawn tens over the 23 unowned modules, **4 viable held-out families and 0 module-disjoint pairs**, so R5's two-held-out minimum is unsatisfiable (ADR-1556; reproduces ADR-1420's draw-17 finding with the blocking core grown from 1 module to 4) |
| 2026-09-02 | nursery-draw-19b | the blindness screen draw 17 lacked, run on every candidate row: `Int.gcd_eq_natAbs` is **`rfl` in this kernel** (`int_prelude/gcd.rs:declare_gcd` builds `Nat.gcd (natAbs a) (natAbs b)` as `Int.gcd`'s value) — invisible to R9 and to R11's vocabulary map, found only by statement shape; recorded as a `do-not-draw-held-out` row that BINDS (viable tens 4 → 3) |
| 2026-09-02 | nursery-draw-19b | `adr-1556-draw-19-screen.py`: exit 0 while the refusal holds, 1 when a disjoint pair appears; the clone-the-blocking-module control did NOT fire (the dedup key is the drawn ten, so a clone collapses onto the original) and was replaced with one that does — 3 viable / 0 pairs becomes 35 viable / 20 pairs |
| 2026-09-02 | nursery-draw-19b | found: the draw-10 `do-not-draw-held-out` judgement on `Mathlib.NumberTheory.{SumTwoSquares,PythagoreanTriples}` lives in a generator COMMENT and is read by no guard — the ADR-1450 shape recurring, on two modules that are in every viable held-out ten today |
| 2026-09-02 | nursery-draw-19b | gates unmoved: both component gates byte-identical before/after, `check-dispatchable-frontier.py` 2/2, census targetable 4/4, `partition-edges --baseline` `violations=0` with the baseline unchanged at 198 |
