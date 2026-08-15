# Diary: catching up `docs/reference/examples.md` to Cargo reality

Lane: `examples-sweep`. Date: 2026-08-15.

Task: `docs/refactor-2026-08` finding #4, "documents assert what the code
does not" — `python3 scripts/check-parity-docs.py` was red because Cargo
examples had landed without a matching row in the example catalog.

## What the gate actually said

Running the gate cold turned up **six** missing examples, not the five named
in the brief:

- `crates/axeyum-cas/examples/geometry_linear_route.rs`
- `crates/axeyum-lean-import/examples/lean4export_census.rs`
- `crates/axeyum-lean-import/examples/nat_add_reduction_probe.rs`
- `crates/axeyum-lean-kernel/examples/arith_model_witness.rs`
- `crates/axeyum-lean-kernel/examples/prelude_build_timing.rs` — not on the
  original list, landed after the brief was written
- `crates/axeyum-solver/examples/ordered_ring_refutation.rs`

All six were `git ls-files`-tracked and the working tree was clean for every
one of them (`git status --porcelain` showed nothing for these paths), so
none of it was another lane's in-flight WIP. I documented all six rather than
leaving the sixth for a future sweep — the gate is what defines "missing,"
not the brief's enumeration, and a lane that stops at the five named files
would hand the gate back red.

## Where each row went

Rows were placed next to their nearest kin rather than appended, so the table
groups stay meaningful:

- `lean4export_census`, `nat_add_reduction_probe`, `arith_model_witness` →
  "Import and trust-boundary tools", next to `lean4export_import` /
  `nat_axiom_inventory` / `theorem_axiom_footprint`.
- `ordered_ring_refutation` → same section, next to `infeasibility_farkas_lean`
  (both are Lean-trust-boundary probes over an LRA/Farkas core).
- `geometry_linear_route` → same section, next to `geometry_obstruction`
  (the two are explicitly a like-for-like comparison of each other's
  counters).
- `prelude_build_timing` → "Maintainer diagnostics": it is an unaggregated
  timing probe ("the example deliberately does no statistics of its own"),
  the same shape as the other rows in that table, not a learning example or
  an artifact generator.

## Writing the rows

Per the brief's standard (state the boundary/question, not the name), each
row was checked against source, not just the `//!` header:

- `lean4export_census`: the fail-closed-importer-samples-one-blocker claim and
  the "27 declines in 4 clusters was 27 first-blocker samples; the real
  census found 10 distinct roots and 61/93 cascades" numbers are in the
  file's own header verbatim — carried through unchanged.
- `nat_add_reduction_probe`: the header states the motivating fix was
  `Proj`/`Proj` congruence in `def_eq`, not the reducer — carried through.
- `arith_model_witness`: verified the "relative consistency, not a
  discharge" framing and the empty-footprint-per-witness mechanism against
  both the header and `main` (`kernel.axiom_footprint(law.witness)`).
- `ordered_ring_refutation`: verified against the header's own worked-out
  claim — 30 `Real` declarations generalized out via
  `generalize_over_ordered_ring`, empty footprint on the generalized
  theorem, non-empty footprint on the original as a printed negative
  control, instantiation recovering the original and kernel-rechecking it.
- `geometry_linear_route`: the header only carries the like-for-like-counters
  framing and the zero-residue short-circuit reasoning; the "4-6 ms vs 27
  minutes" figures came from the brief, so I cross-checked them against
  `docs/plan/status/31-euler-linearity.md` and
  `docs/mathematics-2026-08/diary-euler-linearity.md` before writing them
  into the row — both independently confirm the numbers.
- `prelude_build_timing`: header and `main` both directly support the row
  (five preludes timed per iteration, tab-separated, no on-example
  aggregation).

None of the six examples had a header that failed to explain its own
purpose — that's worth recording since the brief asked for it as a finding,
and here there wasn't one.

## The count marker

`docs/documentation-plan.md` already read "all 67 checked-in Cargo examples"
and `PLAN.md` (generated, via the `{{example-count}}` token in
`docs/plan/status/70-documentation.md`) already read "all 67 Cargo examples."
`len(sorted(ROOT.glob("crates/*/examples/*.rs")))` is 67 right now, so both
were already correct — the six missing files were catalog-row omissions, not
a stale count. Nothing to derive or fix there this time.

## Gates

- `python3 scripts/check-parity-docs.py` → exit 0.
- `./scripts/check-links.sh` → `all links ok`, exit 0.
- `python3 scripts/gen-plan.py --check` → exit 0.

No Rust was touched; no `cargo fmt` was run.
