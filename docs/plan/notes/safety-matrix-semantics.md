# Notes: safety-matrix-semantics

Detail moved out of [`../status/safety-matrix-semantics.md`](../status/safety-matrix-semantics.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

Weaker than the census row it replaced, as S1 said. `UNPINNABLE_PROBE` watches
`statement_pinned_ids()` for an *impossible* id, so two failures walk past it,
both measured surviving at exit 0 with the column still reading 2121/2121: a
constant-`True` `exact_statement` (the probe never reaches `classify`), and a
pin set read from `artifacts/facts` instead of the manifest (a set of real fact
ids contains no probe id). Both now die, by two distinct new controls.

## Asks on other lanes (none touched here)

- **S2** — emit `subjects.resolved` keys into `check-trust-closure.py --json`.
  It builds the set and discards it; publishing it gives `circularity` and
  `per_theorem_footprint` coverage columns at ~1,956.
- **S3** — put `census.load_bearing` into `fixture-pack.json`. The summary
  markdown already renders the map; only the JSON lacks it.
- **S4** — publish the fact→declaration join, so a NAME grade becomes a FACT
  grade. Lands free once S2 emits its set.
- **`F:ordered-ring-farkas-refutation`'s owner** — its `independent_replay`
  evidence is `scripts/check-lean-gate.sh` with no arguments, a gate that says
  nothing about that fact in particular. That is the inheritance ADR-0760's
  exit clause forbids, surviving in a `checker_command`.

## What this audit did not check

It never executed a `checker_command`. Every claim about what a command does is
read from the command text and the source of the tool it names, so a command
naming a real check that fails for an unrelated reason still counts as carrying
its protection here. `scripts/check-fact-evidence-replay.sh` is the instrument
that closes this; joining its per-fact result to the census is the follow-on.
