# Lane: fta-assess — refresh graded-statement-families.md, assess FTA row 3

<!-- plan-section: lane-status -->

**Done (`DONE`, fta-assess, 2026-08-27).** Two tasks, both measurement/doc,
nothing under `crates/` touched:

1. **Refreshed `docs/curriculum/graded-statement-families.md`'s MVT row 3**,
   stale within hours of being written: `polynomial_mvt`/
   `verify_mvt_certificate` (`crates/axeyum-cas/src/mvt.rs`) landed the same
   day the row still read "reachable, not built." Re-ran the suite fresh
   (`cargo test -p axeyum-cas --lib mvt::` — 18 passed, 0 failed) rather than
   trusting the landing lane's own report, updated row 3, the MVT verdict,
   and the "what this changes" pointer. Re-confirmed EVT row 2 is still
   "in progress" per `extremum.rs`'s own module doc (a separate lane is
   building that refutation in `creal/extreme_value.rs`; not yet landed at
   merge time, outcome not guessed). Mirrored the correction into
   `spivak.md` row 11. `cargo test -p axeyum-cas --lib extremum::`
   re-confirmed 20 passed, 1 ignored (unchanged from the note's own claim).

Detail moved to [`../notes/142-fta-assess.md`](../notes/142-fta-assess.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | `DONE` | `graded-statement-families.md` MVT row 3 refreshed to landed; FTA row 3/row-2-applicability independently re-assessed with fresh positive/negative controls, a sized cheapest-route estimate (RUR), and a finding that FTA may be a three-row theorem with no row 2; `spivak.md` row 11 corrected to match. |
