# Lane: avg-pair-constructions — execute ADR-1045's named draw-12 unblock

<!-- plan-section: lane-status -->

**Status: DONE.** Decision record:
[ADR-1060](../../research/09-decisions/adr-1060-declare-nat-avg-and-nat-pair.md).

Declared both constructions ADR-1045 asked for. `Nat.avg`/`Nat.pair`
exactly as specified (`avg_pair.rs`), plus a SECOND construction —
`Max.max`/`Min.min`/`Nat.instMax`/`instMinNat` (`minmax.rs`) — that ADR-1045
flagged as the "largest remaining opportunity" but sized as the harder
route (Mathlib states `Init.Data.Nat.MinMax` through a typeclass this
kernel does not model). Simulated first in both cases, then built,
construction-only (ADR-0653: definitions and an evaluation test, nothing
else — verified by grep, no theorem declared in either file).

Re-screened AFTER declaring, against the REAL post-build kernel
environment (fresh `shape_search --release`, 2572 declarations, not a
simulated one): both families R9 0/10, R11 clean, R5's two-new-family
minimum satisfied. `artifacts/autogenesis/` untouched throughout —
`check-autogenesis-holdout-isolation.py` reports `held_out=146|verdict=PASS`
identically before and after (necessarily, since nothing it reads changed).
`gen-autogenesis-nursery-refill.py --check` still reports `entries=380`
against the committed snapshot, byte-identical to ADR-1045's own report.

`nat_prelude::` sweep: 268 passed, 0 failed (was 264 on the parent commit;
+4 for the two new definitions' coverage in `definition_names`, +5 for the
new test files, net of the fix that closed a coverage gap the environment-
derived `every_nat_declaration_is_checked_and_axiom_free` assertion caught
on the first build). Clippy clean on every file this lane touched
(4 files: `avg_pair.rs`, `avg_pair_tests.rs`, `minmax.rs`,
`minmax_tests.rs`); 7 pre-existing clippy errors remain elsewhere in the
crate, untouched by this lane, out of scope.

**Next draw needs:** author draw 13 — add `natural-avg-pair`/
`natural-minmax` (or whatever names the drawing lane picks) to
`FAMILY_MODULES`/`FAMILY_ROUTES` in `gen-autogenesis-nursery-refill.py`,
regenerate the manifest, reconcile the fact ledger. This lane deliberately
did not touch that file or `artifacts/autogenesis/` — it enabled a draw,
it did not author one.

<!-- plan-section: landed-changes -->

| 2026-08-31 | avg-pair-constructions | `Nat.avg`/`Nat.pair` construction + evaluation tests (ADR-1045's named unblock) |
| 2026-08-31 | avg-pair-constructions | `Max.max`/`Min.min`/`Nat.instMax`/`instMinNat` construction + evaluation tests (second held-out family, ADR-1045's "harder route", taken) |
| 2026-08-31 | avg-pair-constructions | ADR-1060: both re-screened against the real post-build environment, R9/R11 clean, R5 satisfied |
