# Lane: board-fpbv — the three untested FP/array and UF/BV divisions

<!-- plan-section: lane-status -->

**Lane board-fpbv (`DONE`, board-fpbv, 2026-09-12).** `QF_ABVFP` (18,129 files),
`QF_BVFP` (17,249), `QF_UFBV` (1,510) — **36,888 files** — had never carried a
parity row. They do now; the board goes from 20 of 84 SMT-LIB divisions to 23.
Pure measurement: **no solver code changed.**

    division    files   axeyum   z3   cvc5
    QF_BVFP     17,249     199   200    197
    QF_ABVFP    18,129     179   197    198
    QF_UFBV      1,510      89   174    162
    total                  467   571    557   (of 600)

**The `REACHED-SOLVER` label in `blockmap.txt` is CONFIRMED at n=200 on all
three**, and it understated `QF_BVFP`, which decides 199/200 and beats cvc5.
Nothing in these divisions is structurally blocked.

**Soundness: 0 disagreements across all 1,800 solves**, on three independent
checks, and none vacuous — every division is comparable on ≥ 97 % of what it
decides against the declared `:status`, z3 4.13.3 and cvc5 1.3.4.
Reference-vs-reference conflicts 0. **0 wrapper-killed rows on any solver in any
division.** (cvc5 has 38 `rc134` on `QF_UFBV` — the protocol's 8 GiB cap — so its
162 is a depressed floor, not its capability.)

Lists pinned at `04e0df4ac` **before** anything ran. Boards at `3a536570f`
(QF_BVFP), `64169d76f` (QF_ABVFP), `7c1083441` (QF_UFBV).

**The three divisions gave three different answers, which is the point of the
census:**

1. **QF_BVFP needs nothing.** 199/200.
2. **QF_ABVFP is one bug, not a capability gap.** 16 of 21 winnable files stop
   in `abv-online-cdclt` with 24.6–25.0 s of a 25 s budget in an unattributed
   open segment. At a **600 s** budget — 25x — it still reports
   `online_returned=0 cegar_rounds=0` on a `row_sites=4` query both references
   decide in 0.11 s. Not slow: not reaching its first round. Repro committed.
3. **QF_UFBV is two constants.** **84 of 87 winnable files (97 %)** are stopped
   by `MAX_THEORY_ATOMS = 1_024` (53) and `MAX_INPUT_DAG_NODES = 16_384` (31),
   adjacent lines in `crates/axeyum-solver/src/ufbv_online.rs`. Only 2 of 87 are
   real budget exhaustion. Over-cap magnitudes are 1.04x–5.33x (atoms) and
   1.00x–14.04x (nodes).

No division on this board points at a decision procedure we lack — itself a
finding, since that was the plausible prior for three untested divisions.

**A second defect with a repro:** one QF_ABVFP file returns `backend failure:
array projection element sort mismatch: read site produced (_ BitVec 32) for an
array whose element sort is (_ FloatingPoint 8 24)`. Both references decide it.

Both defects are **sound** — each returns `unknown` — and cost coverage, not
correctness. Neither is fixed here; each should be its own lane.
`bench-results/fpbv-divisions-headtohead-20260912/findings/README.md`.

**Next actions for whoever picks this up.** (a) Fix `abv-online-cdclt`'s
non-progress; `winnable/QF_ABVFP.txt` is the pinned A/B population and 16 files
is the size of the prize. (b) A/B the two `ufbv_online.rs` caps over
`winnable/QF_UFBV.txt` — **not a raise-and-ship**: a cap converts a slow
`unknown` into a fast one, and the 2 rows that did exhaust the budget are the
warning. (c) The `array projection element sort mismatch` repro.

**[ADR-1941](../../research/09-decisions/adr-1941-attempts-alone-cannot-classify-a-census-row-the-open-segment-is-the-discriminator.md)
came out of this lane, and the QF_UFBV finding depends on it.** ADR-1936 says a
census must mark `UNCLASSIFIED` any row whose dispatch did not reach the end of
the ladder — but a census cannot observe the ladder length, only the maximum
`attempts=` it saw. Using that proxy called **77 of 87** QF_UFBV rows
unclassified and would have suppressed the 53-file single-constant finding
entirely. The discriminator is a field already being printed: **87 of 87 rows
have no `route-open` segment** and `bound_ms` ≈ `total_ms`, so they ran to the
end of a *shorter* ladder — rung count is query-dependent, and rows at
`attempts=14` and `attempts=18` end on the same reason. QF_ABVFP's 19 rows,
which carry a 24.98 s open segment, stay `UNCLASSIFIED`. Both readings are now
published side by side on every division.

The two checkers are mutation-tested: **nine mutants, nine kills**, including
two that revert ADR-1941 and one that publishes only one of its two readings.
`controls/run-controls.sh`, `controls/mutants.py`.

<!-- plan-section: landed-changes -->

| 2026-09-12 | board-fpbv | First parity rows for QF_ABVFP / QF_BVFP / QF_UFBV (36,888 files): 179 / 199 / 89 of 200 vs z3 197 / 200 / 174, **0 disagreements, 0 wrapper kills**; ADR-1941; two defects with repros; QF_UFBV is 84 of 87 two constants |
