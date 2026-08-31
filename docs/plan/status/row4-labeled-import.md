# row4-labeled-import

<!-- plan-section: lane-status -->

**Status: DONE.** ADR-0603 row 4 (labeled import) was the only row ABSENT for
both IVT and EVT in `08-ivt-and-evt-measured-against-mathlib.md`. It now
exists for both, sourced from Mathlib itself.

## What was verified before building

- `scripts/check-lean-gate.sh --print-toolchain` and
  `scripts/provision-lean-import-toolchain.sh --verify` both PASS on this
  host (elan-pinned toolchain, not on `PATH` — the empty `command -v lean`
  false-negative CLAUDE.md warns about). mathlib4 checked out at the pinned
  commit `c5ea00351c28e24afc9f0f84379aa41082b1188f` with oleans pre-built.
- Read `F:bool-and-comm` and the other four `imported-kernel-lean` facts in
  full as the template for row 4's mechanism, rather than inventing a shape.
  Confirmed all five prior imports were Lean `Init`-only — this lane's two
  facts are the first sourced from Mathlib.

## What landed

- `lake env lean4export Mathlib.Topology.Order.IntermediateValue --
  intermediate_value_Icc` and the EVT analogue
  (`Mathlib.Topology.Order.Compact -- IsCompact.exists_isMaxOn`), each
  pulling the theorem's FULL transitive dependency closure. Both admit
  through `Kernel::add_declaration` with **zero declines**: 3,142/3,585 and
  2,171/2,486 (records/admitted).
- Two new facts, `F:ivt-mathlib-import-intermediate-value-icc` and
  `F:evt-mathlib-import-compact-exists-is-max-on`, `proof_route:
  imported-kernel-lean`, `epistemic_status: proved` (the kernel independently
  admitted the term), non-empty `axiom_footprint`, never counted as ours.
- Two new `Row` entries in `imported_fact_evidence.rs` (now 7 total) so both
  facts' `kernel-term` evidence re-derives on every run.
- `scripts/check-imported-fact-lean-axioms.sh` gained a `MATHLIB_ROWS` table
  and a `lake env lean` code path (a bare `lean` cannot resolve a Mathlib
  name), cross-checking both theorems' axiom footprint against a real Lean
  4.30.0 binary independently of the kernel. Both report `[propext,
  Classical.choice, Quot.sound]`, matching `08-…`'s existing measurement and
  ADR-1030 exactly, and matching 3 of the kernel's 8 (the other 5 are the
  Quotient-package split plus two real trusted declarations — a
  `String.Internal.append` opaque and a `wrapped._@...Filter...` opaque —
  this closure reaches that the five `Init`-only facts never did).
- [ADR-1090](../../research/09-decisions/adr-1090-ivt-evt-row-4-labeled-import-lands-mathlib-topology-admits-clean.md)
  and dated correction blocks in `08-ivt-and-evt-measured-against-mathlib.md`
  (table row, both "Row 4 — absent" section headers, "What actually remains
  for EVT"), following the document's own convention: append a correction,
  do not silently rewrite stale prose.
- `artifacts/lean-imports/MANIFEST.json` gained the two new stream entries
  plus a `reproduction_mathlib` block (the existing `reproduction` block is
  `Init`-only and does not apply).

## What this is NOT

Not a claim this project proved IVT or EVT — `proof_route` is
`imported-kernel-lean`, `axiom_footprint` is non-empty by construction (the
validator rejects `[]` on this route), and neither fact counts toward any
axiom-free or originated headline. Not a change to ADR-1030's per-statement
Pareto verdict (IVT dominant, EVT conceded) — row 4 supplies the labeled
scaffolding statement, it does not re-argue dominance.

## Re-verification performed

- `cargo test -p axeyum-lean-import --test imported_fact_evidence --
  --nocapture` — 1 passed (26 s), all 7 rows print their marker and re-derive
  cleanly.
- `scripts/check-imported-fact-lean-axioms.sh` (no filter, all 7 rows) — 7
  cross-checked, 0 failed.
- Negative controls, both in `scripts/lane-snapshot.sh` scratch copies (never
  the tracked tree): mutating the IVT row's `declaration` name to a
  nonexistent one aborts the whole test process, so BOTH new facts'
  `checker_command`s correctly exit nonzero (grep count 0 for each);
  mutating the pinned expected axiom set in a scratch copy of the shell
  script makes it exit 1. Both restored before committing.
- `cargo clippy -p axeyum-lean-import --all-targets --all-features -- -D
  warnings` — clean (fixed `needless_raw_string_hashes` on the two huge
  pinned type strings: no `"` in the content, so `r"..."` not `r#"..."#`).
- `python3 scripts/validate-facts.py` — 2380 facts, 0 errors,
  `imported-kernel-lean=7` (was 5).
- `python3 scripts/check-settled-fact-statements.py --write` then bare —
  PASS, additive-only diff (12 lines).
- `python3 scripts/check-mirror-statement-fidelity.py` — PASS, unaffected
  (these facts are not `F:ml430-*`).
- `python3 scripts/gen-adr-index.py --check` — exit 0, no new duplicate
  numbers (`0166,0167` pre-existing, grandfathered).
- `bash scripts/check-links.sh` — all links ok.
- `scripts/check-merge-hygiene.sh` — PASS.

## Cost note for the next Mathlib-sourced import

`artifacts/lean-imports/` gained two large fixtures (9.9 MB, 6.2 MB) — real
cost of a Mathlib dependency closure versus the ~50-1,100 record `Init`
facts. Expect a similar closure size (low thousands of records) for the next
target, and reuse `scripts/check-imported-fact-lean-axioms.sh`'s
`MATHLIB_ROWS` mechanism rather than rebuilding it.
