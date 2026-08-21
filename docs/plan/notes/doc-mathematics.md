# Notes: doc-mathematics — every claim corrected in `docs/mathematics-2026-08/`

Detail kept out of [`../status/70-doc-mathematics.md`](../status/70-doc-mathematics.md)
so the lane block stays inside the per-lane ceiling (ADR-0520).

## Method

Correct claims, do not rewrite the strand. Where a passage advised against work
that has since been done, the old sentence stays on the page — struck through or
quoted — beside what was built, when, and under which ADR. A strand doc that
silently loses the argument it used to make is worse than one that is out of
date. Every number below was re-measured in this lane; none was copied from a
status file or a doc.

## Measurements (2026-08-19, HEAD `51fdc0ae6`)

| quantity | command | value |
|---|---|---|
| trusted surface, all preludes | `--example nat_axiom_inventory -- --include-constructed` | `complex 0 · creal 0 · integer 0 · logic 0 · nat 0 · rat 0 · string 0 · real 30` |
| `Real` axiom rows | `--example prelude_axiom_inventory` | 30, every one `real` |
| ℝ declarations | `--example creal_setoid_witness` | 94, trusted surface 0, all 22 ordered-ring laws |
| ℂ declarations | `--example complex_ring_witness` | 39, trusted surface 0, 9/9 ring laws, order refuted |
| ℕ theorems | `--example nat_theorem_inventory` | 139 (the strand said 106) |
| ℤ theorems | `--example int_theorem_inventory` | 57 derived, 57 footprint-empty, 0 asserted |
| front-door carrier | `--example front_door_carrier` | `CReal` on all three fixtures; footprints 3/5/2, **0** carrier axioms, against 12/17/8 over `Real` |
| facts | `artifacts/facts/*.json` | 340 total; 120 settled (115 `proved`, 3 `refuted`, 2 `computed`) |
| ADRs | `docs/research/09-decisions/adr-*.md` | 523 |

Absence was checked by enumerating the declared names, not by grepping prose:
`CReal` has no `sqrt`, no `sup`, no completeness, no cotransitivity, no
`apart_mul`; `Complex` has no `inv` and no `abs` (it has `conj`, `normSq`,
`mul_conj`, `normSq_nonneg`).

## Claims corrected, old → new

**`02-the-library.md`** — the file the brief named.

- *"**ℝ is a different order of effort** and should be scoped, not attempted"* →
  ℝ was built under ADR-0512, with the original reasoning kept and the part of it
  that survived named: completeness really is a different obligation and really
  is still unbuilt; what the reasoning missed is that ordered-field structure
  does not wait on it.
- *"**Do not start ℝ** without an explicit decision. Scope it, cost it"* → the
  instruction was **followed**: ADR-0512, plus 0510/0516 (inverse), 0519
  (lattice), 0521 (ℂ). Item recast as a record, not deleted.
- *"ℝ | Cauchy sequences or Dedekind cuts over ℚ"* → a Bishop setoid of regular
  ℚ-sequences under a defined `CReal.Equiv`, with a new **ℂ** row (the cheapest
  rung on the table).
- The `nat 106 / int 0-of-3 / arith 0-of-3 / string 1` state block kept as the
  2026-08-15 reading, with a measured 2026-08-19 block beside it.
- "Assumptions remaining … Today: `int` 3, `arith` 3, `string` 1, `nat` 0" →
  measured all-zero row plus `real 30`, with why 30 stays (ADR-0509).
- "What to do first" items 1, 2, 4, 5 marked done or superseded; a new
  **not built** table with costings reused from `creal-field.md`,
  `creal-inv.md`, `creal-lattice.md`.

**`README.md`** — new dated status ahead of the 2026-08-15 one; rung 5 of the
ladder table gains its 2026-08-19 reading; "four documents" heading listed five.

**`03-symbolic-and-infinite.md`** — *"ℤ is axiomatized … inherits them"* and
*"ℤ constructed rather than assumed"* were the library-shaped third of a
three-part diagnosis. Corrected, and the point made that the other two thirds
(a finite problem is a formula; chains not subsets) are now the **whole** of the
answer.

**`04-reachability.md`** — `string` row 1 → 0 (ADR-0513, retired 2026-08-17), so
"Total: 31" → 30, all ℝ; `rat`/`creal`/`complex` rows added. The "this lane
could not run cargo" caveat is discharged by running both commands. R4 step 3's
choice was taken, the second way. The closing frontier paragraph goes from "two
number systems constructed … and one still axiomatised" to five constructed,
with a new note on what still bounds *statability*: analysis, not axioms.

**`05-the-mathematics-dag.md`** — D3 was ordered second so it would be read
*before* months were spent on ℚ and ℝ. Both were built first and neither took
months, so D3 is re-scoped rather than dropped: from a check on a plan to a
standing coverage measurement against Mathlib, including which of its
constructions are unavailable to a kernel with no `Quot.sound`, `propext` or
`funext`. It stays second. `nat_prelude` 106 → 139.

**`01-decide-vs-certify.md`** — the quoted `qf_rdl_difference` gate transcript
shows the `Lra` route resting on `[Real, Real.add, …]`. `QF_RDL` still routes
through `ProofFragment::Lra` (the test asserts it), but that fragment's carrier
is `CReal` since ADR-0512, so the axiom line is the query's own hypotheses. The
`Real` column is kept as the non-vacuity control; the cost is module size, 58×
to 455×.

**`diary-real-keystone.md`** — a dated record, left as written, with two
insertions. Its pull quote *"A Cauchy-sequence construction of ℝ … is
inexpressible"* is wrong by one word: the **quotient** is inexpressible, the
construction is not, and ADR-0512 is exactly that distinction. Its two
measurements (no `Quot.sound`; no `propext`/`funext`) were right and are what
forced the setoid. A "what happened next" footer records that both of its
recommendations were followed and that its ℚ prediction was overtaken by a step
it could not have seen — `Rat.inv` existed as a definition with no law about it.

## Left alone, deliberately

- The other 16 diaries. They are dated records of specific results and none of
  them makes a current-tense claim about ℝ or ℂ (checked by grep across all of
  them for `ℝ is` / `ℝ was` / `construct ℝ` / `ℝ needs`).
- `02`'s two hazards (`nat_prelude.rs` `.expect`, the O(n³) permutation prover).
  Still open; nothing in this work retires them, and they are not this lane's.
- `04`'s R1/R2/R3 census numbers and `05`'s graph counts. Out of scope, and the
  `math-education` graph is a sibling repository this lane did not measure.
- `01`'s capability tables and band rankings.

## What the brief got wrong

- It said `check-parity-docs.py` "currently has 17 errors, all inherited from
  main". Measured at lane start: **21**, all in `docs/reference/examples.md`,
  `docs/documentation-plan.md` and `PLAN.md`. It read 19 at lane end — another
  lane lowered it mid-session. None is in this strand either way.
- It described `CReal.inv` as *"a partial multiplicative inverse"* among the 94,
  which is right — but `notes/creal-field.md`, one of the three notes it sent me
  to for costings, still says **"`CReal.inv` is not built. Here is the design and
  what it costs"**. `creal-inv.md` supersedes it and `creal_setoid_witness`
  confirms `CReal.inv` and `CReal.mul_inv_cancel` are both admitted. Anyone
  reusing that note's costings should take the *undone* rows (cotransitivity,
  `apart_mul`, completeness) and ignore its inverse section.
