# Lane `lean-creal-library` — publish the constructive analysis as a Lean library

<!-- plan-section: lane-status -->

**Next Ten item 3** of [`docs/math-department/14-lean-lang.md`](../../math-department/14-lean-lang.md):
render the `creal` prelude as `.lean` source that pinned Lean elaborates, with
`#print axioms` empty on the Lean side, packaged for Lake. Reviewer 02
(constructive analysis) calls the shelf "among the most complete constructive
real analyses anywhere"; until this lands, nobody outside this repository can
`import` a line of it.

**What exists before this lane.** The replay census (ADR-1661,
`artifacts/measurements/lean-replay-census-2026-09-05.md`) hands pinned Lean's
*kernel* the `lean4export` NDJSON stream and grades every `creal` declaration by
name: 3,542 of 3,617 accepted, 49 `Type`-valued theorems Lean refuses as
theorems, 26 blocked behind five of them. That is a census artifact, not a
library.

**The shape of the answer.** Lean *source* has a way out the wire format does
not: a `Type`-valued proof is an ordinary `def`. So the source route publishes
strictly more of the development than the wire route can, and the census's 3,542
is the floor the gate enforces rather than the target.

**Status.** In progress. The generator
(`crates/axeyum-lean-kernel/examples/render_creal_library.rs`) and the gate
(`scripts/check-lean-creal-library.sh`) are written; the numbers in this file
are the census's, not this lane's, until the first full `lake build` runs.

<!-- plan-section: landed-changes -->

| date | commit | what |
| --- | --- | --- |
