# Lane: bench-primitives — benches and a profile for the three shared primitives

<!-- plan-section: lane-status -->

**Five bench targets across the three shared primitives, four findings, and
five recorded mistakes** (`DONE`, bench-primitives, 2026-09-07).

`axeyum-bv` and `axeyum-smtlib` had **no benches at all**; `axeyum-ir` had one.
They now have `bv_lowering`, `smtlib_parse`, `term_eval` and `value_bits`
beside the existing `arena_intern`. Every group names, in its own module doc,
the real workload it stands for — or says plainly that it has not been shown to
predict anything.

The findings, with evidence in the diary
([`docs/research/12-performance/bench-primitives-2026-09-07.md`](../../research/12-performance/bench-primitives-2026-09-07.md)):

1. **`BitLowering::input_values` is quadratic in symbol width**, predicted in
   the bench's doc comment before the run and confirmed: `t = 16.4·w + 0.483·w²`
   ns fits four widths within 3%. **97%** of it is one redundant call —
   `value_to_lsb_bits` allocates a full-width `Vec<bool>` per symbol *bit* and
   reads one bit from it. The quadratic survives the `Value::Bv` →
   `Value::WideBv` code-path crossing, so it is the caller's loop, not a
   conversion routine. 631 µs per replay at width 1024. **Counterweight, in the
   same bench group:** on the committed corpus it is 11.9 µs against 577 µs of
   lowering — 2.1%, a rounding error. Real, cheap to fix, low priority at the
   widths the corpus contains.
2. **SMT-LIB ingest is linear in bytes at 30–58 MB/s across four orders of
   magnitude**, so the in-tree "58 MB takes ~54 s" figure that justifies the
   ingest deadline is **~30x** off what these numbers predict (linear says
   ~1.9 s). Both can be true — that file's shape, staleness, or a wider meaning
   of "reading" — but the figure must not be quoted as a bytes-per-second rate.
   Unsettled: the file is not in the tree.
3. **The s-expression reader is 29–60% of ingest**, and its share tracks file
   *shape*, not size. A faster typed parser is capped at roughly half of ingest.
   `read_all` materializes the whole `SExpr` tree, one owned `String` per atom,
   before the typed pass starts.
4. `eval`'s fresh per-call `FastMap` costs **14.5–16.6%** of a replay loop.

**`bv_lowering` deliberately does not compare memo representations.** ADR-0300
preregistered exactly that `BTreeMap` → dense experiment and rejected it on a
run-total variance gate despite a 0.922 paired bit-blast geometric mean; it
also names microbenchmark selection among its rejected alternatives. This lane
had drafted it as a new finding before reading the ADR (W3 in the diary).

**Variance is the standing caveat**: two runs minutes apart at load < 1.5 differ
by up to ±20% on the allocation-heavy benches, well outside criterion's
own sub-1% intervals. Nothing here should be quoted to two significant figures;
the findings are ratios and shapes because those survive it.

Did not run, reported as such: a controlled hasher A/B (W4 — the 4.0x against
the 2026-09-05 `arena_intern` baseline is **not** comparable, loads differ by
an order of magnitude); the 58 MB file behind finding 2; `write_script`; what
fraction of a whole solve model replay is; the demanded/range-demanded routes.

<!-- plan-section: landed-changes -->

| 2026-09-07 | bench-primitives | `smtlib_parse`: `read_all` and `parse_script` over four committed files, 2.7 K to 10.5 M. Opens the lane diary under `docs/research/12-performance/`. |
| 2026-09-07 | bench-primitives | `bv_lowering` (first benches in `axeyum-bv`) and `term_eval` + `value_bits` in `axeyum-ir`; `input_values` sweep carries a falsifiable quadratic prediction in its doc comment. |
| 2026-09-07 | bench-primitives | Diary written up: four findings, five recorded mistakes, the ±20% between-run variance envelope, and the did-not-run list. |
