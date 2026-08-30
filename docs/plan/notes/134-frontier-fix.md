# Notes: 134-frontier-fix

Detail moved out of [`../status/134-frontier-fix.md`](../status/134-frontier-fix.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**Curriculum.** Did not edit `docs/curriculum/curriculum.toml`. This week's
~30 new `proved` `CReal`/`Complex` facts (uniform convergence, alternating
series, polynomial evaluation, Complex factor-quotient/Horner form) map onto
`sequences-and-limits`/`calculus`/`complex` — three nodes that already exist,
currently `status = "lean-horizon"` on the SOLVER axis (no `axeyum-scenarios`
family). Adding finer nodes would each need a real `gen-foundational-
concepts.py` `CURRICULUM_MAP` entry naming an EXISTING example pack, which
none of the plausible finer topics has yet; asserting one without a pack
risks exactly the "asserts coverage it cannot demonstrate" defect
`check-curriculum-coverage.py` exists to catch. Recorded as a finding in doc
288 instead of a curriculum.toml edit.

**Next, for whoever has s5/Mathlib iteration time.** Doc 288 names four
sibling `Int.ModEq` facts already dependency-ready
(`F:ml430-int-modeq-add-left-6e17c69a`, `-neg-f649f6c5`, `-of-dvd-b9c41fce`,
`-sub-3148f130`) as the best next candidate for a genuinely general
multi-target operation, since the shape-generic checker
(`modeq_family_operation`, declines by typed `UnsupportedRecursorShape`/
`UnsupportedIffShape` rather than fixed theorem names) already exists and
only needs new s5-side Lean exports for these four targets. Separately,
`F:fp16-add-monotone-rne` is the one open fact reachable by pure compute (no
new proof needed) — worth a bounded, explicitly-timed attempt at the existing
`smtcomp_cli` route.
