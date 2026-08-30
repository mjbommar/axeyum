# Lane: ledger-trig — register Spivak Ch.14/15/22-23/25-27 facts (crossing, cosOne, ratio test, polynomials)

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, ledger-trig, 2026-08-27).** Registered 28 new
facts in `artifacts/facts/` for mathematics that had been built in this
kernel across four sibling lanes' work (`creal/trig.rs`,
`creal/ratio_test.rs`, `creal/crossing.rs`, `crates/.../src/complex/poly.rs`)
but had no ledger entry.

**Ch.15 (trigonometry, the kernel's first transcendental value):**
`F:creal-cosone` (the CONSTRUCTION, via `CReal.mk` on an explicit regular
sequence, never `Exists`-elimination), `F:creal-costerm`,
`F:creal-cosseriespartial`, `F:creal-costermabsledominant`,
`F:creal-cosoneconverges`, `F:creal-cosone-le-four`,
`F:creal-neg-four-le-cosone`. The last two are recorded as what they are: a
LOOSE, uniform `[-4,4]` bound (no case split, unlike `e_le_three`'s genuine
kink at index 2), reusing `CReal.e`'s domination unchanged and discarding
the alternating series' sign cancellation via the triangle inequality — it
does not pin `cos(1)`'s sign, let alone approximate `cos(1) ~= 0.5403`. Both
facts' `statement` and `notes` say this explicitly.

**Ch.22-23 (series):** `F:creal-geomcauchyoflt`,
`F:creal-geomcauchyofltordered`, `F:creal-geomscaledcauchyoflt`,
`F:creal-sumrangeratiotest`.

Detail moved to [`../notes/132-ledger-trig.md`](../notes/132-ledger-trig.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | (uncommitted at status-file write time) | Registered 28 new `artifacts/facts/F-*.json` entries: Ch.15 cosine-at-1 construction and bounds (`creal-cosone`, `creal-costerm`, `creal-cosseriespartial`, `creal-costermabsledominant`, `creal-cosoneconverges`, `creal-cosone-le-four`, `creal-neg-four-le-cosone`); Ch.22-23 general-ratio geometric series and ratio test (`creal-geomcauchyoflt`, `creal-geomcauchyofltordered`, `creal-geomscaledcauchyoflt`, `creal-sumrangeratiotest`); Ch.14 crossing-index construction (`creal-crossingindex`, `creal-crossingupper`, `creal-crossinglower`, `creal-crossingsampleupper`, `creal-crossingsamplelower`); Ch.25-27 polynomials over `Complex` (`complex-polyeval`, `complex-polyeval-zero`, `complex-polyeval-succ`, `complex-polyadd`, `complex-polyeval-polyadd`, `complex-polyscale`, `complex-polyeval-polyscale`, `complex-polydegreelt`, `complex-polydegreelt-polyadd`, `complex-polydegreelt-polyscale`, `complex-polymul`, `complex-polyeval-polymul`). `python3 scripts/validate-facts.py` green (750 facts, 0 errors). Mutation-tested 3 representative checkers (1 definition, 2 theorems) in an isolated snapshot; all failed correctly on the mutated name while unrelated controls in the same rebuild passed. |
