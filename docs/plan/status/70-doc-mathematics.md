# Lane: agent-doc-mathematics — the mathematics strand, corrected to what exists

<!-- plan-section: lane-status -->

**`docs/mathematics-2026-08/` said "do not start ℝ"; ℝ and ℂ are built, and the
strand now says so without losing the argument it used to make (`WIP`,
agent-doc-mathematics, 2026-08-19).** Seven files corrected in place — old text
struck through and left visible, new text dated and sourced to a command. The
load-bearing numbers were re-measured, not copied: `nat_axiom_inventory
--include-constructed` gives `complex 0 · creal 0 · integer 0 · logic 0 · nat 0
· rat 0 · string 0 · real 30`; `creal_setoid_witness` 94 declarations;
`complex_ring_witness` 39; `nat_theorem_inventory` **139** where the strand said
106; `int_theorem_inventory` 57 derived / 0 asserted; 340 facts (120 settled),
523 ADRs.

Three corrections were not in the brief and came out of measuring. `04`'s
trusted-surface table still carried `string 1` (retired 2026-08-17, ADR-0513),
so its "total 31" is now 30 and all of it ℝ. `01`'s quoted `qf_rdl_difference`
gate transcript still shows `[Real, Real.add, …]`; the shipped `Lra` route
reconstructs over `CReal` and `front_door_carrier` measures 0 carrier axioms
against 12/17/8 for the control. And `diary-real-keystone.md`'s conclusion — *"a
Cauchy-sequence construction of ℝ … is inexpressible"* — is wrong by one word:
the *quotient* is, the construction is not, which is exactly what ADR-0512
exploited. Its two measurements were right and forced the design.

`check-links.sh` green; `check-parity-docs.py` 19 errors, none in this strand
(21 at lane start, lowered by another lane).
[Notes](../notes/doc-mathematics.md).

<!-- plan-section: landed-changes -->

| 2026-08-19 | `e9f5cf287` | **The mathematics strand stops advising against work that is finished.** `02` gains a dated ℝ/ℂ status block, a `ℂ` row and a corrected `ℝ` row in the construction-order table, measured prelude counts, and a "not built" table with reused costings (cotransitivity ~400 lines, `apart_mul` ~300, completeness/`sqrt`/suprema uncosted, ℂ `abs` downstream of both). `05`'s D3 is re-ordered rather than deleted: it was a pre-flight check on a construction order that has since been walked, and is now a coverage measurement against Mathlib. `04` closes R4 and keeps the 30 `Real` axioms as the ADR-0509 negative control. `01`, `03`, `README` and `diary-real-keystone.md` corrected in place. |
