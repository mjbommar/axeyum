# Notes: 118-external-coupling

Detail moved out of [`../status/118-external-coupling.md`](../status/118-external-coupling.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**Not internalized, deliberately.** Re-pointing the 24 edges at local
`C:factorial`-style entities keeps their shape and moves their semantics
nowhere: an axeyum-local `C:factorial` means "whatever the sibling means", with
nobody here to adjudicate it. That is the coupling laundered through a rename,
and it would pass the new gate while the authority still lived elsewhere.
ADR-0553 records the prerequisite instead: **a concept vocabulary this
repository owns is required before a `formalizes` edge can mean anything**, and
the three guards that went with that relation must return with it.

The gate names mechanisms, not repositories, so a different sibling is caught
too: the external-declaration vocabulary (including inside a schema enum), any
`..` path segment in any string, a 40-hex revision under a key not in a registry
that says which repository it pins, and source that builds a path out of the
checkout across `scripts/`, `python/` and `tools/`. Measured: **1,885 artifacts,
159,474 strings, findings=0** here — and **64 findings** over the four real
pre-change artifacts read from `56eaab2cc`, which is the positive control. R4
restored the deleted 777-line module and fired on its first constant.

R3 does **not** forbid a foreign pin — Mathlib, the Lean toolchain and
lean4export are pinned on purpose. It forbids an *undeclared* one.

**Next, and it is the largest known gap:** 1,174 absolute paths in
`artifacts/**` are deliberately uncovered. They record where a measurement
physically ran (`/nas3/...`, `/home/mjbommar/lean-import-scale/...`), which is
provenance rather than a dependency, and forbidding them is a separate policy
question with a 1,174-row blast radius. If that policy is wanted, it is its own
ADR and its own lane.

Two downstream artifacts went **structurally empty** when the `formalizes`
links went, and were reduced rather than left reporting zero — the concept
coverage projection's validator had degenerated to comparing two empty sets, a
check that cannot fail. Ten of fifteen census rows are now *named* instead of
printed as zeroes.
