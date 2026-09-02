# Lane: shape-census

**Status:** in progress — measuring the shape of the 209 `proof-route-only`
dependency-ready open facts, so the next target-agnostic producer can be
designed against a measured population rather than an assumed one.

## Task

Build `scripts/frontier-shape-census.py`: parse each ready fact's
`formal.statement` into a shape signature, bucket at two granularities, rank,
and write `artifacts/autogenesis/frontier-shape-census-v1.json` with a
`--check` mode. Report the finding in
`docs/research/11-design-review/2026-09-02-what-the-frontier-is-shaped-like.md`.

This lane measures. It does NOT write a producer or a contract.

## Landed changes

(none yet — this is the early stub commit required by the brief)
