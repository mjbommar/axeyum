# Lane: nested-array-ir — the nested array sort, sized before it was built

<!-- plan-section: lane-status -->

**Lane nested-array-ir (`DONE — measured, not built`, nested-array-ir,
2026-09-13).** The brief called the nested array sort "the single largest mass
behind one decision": **29,564 files** across AUFLIRA / ABV / ALIA / AUFNIRA,
none of which had a decide-rate measurement of any kind. It is the largest mass.
It is not behind one decision, and the design that fixes it decides **zero
files on its own**. [ADR-1955](../../research/09-decisions/adr-1955-the-nested-array-sort-is-the-first-of-three-gates-and-the-only-one-the-ir-owns.md).

**The blocked count is 27,150, not 29,564** — all 29,564 files through the real
parser, and `nested array element sort` is not the largest parse failure in
these divisions but the **only** one. A second instrument sharing no code with
the parser (a textual s-expression scan with alias expansion) returns
18,644 / 4,502 / 3,028 / 976 — identical in all four.

**A FLAT array already fails for 19,620 of them.** The read-over-write
obligation at a symbolic index, with no nesting anywhere in the query:

    (Array Int Int)                          unsat
    (Array (_ BitVec 64) (_ BitVec 64))      unsat
    (Array Int Real)                         UNKNOWN

`auto.rs:6098` requires `!features.has_real`. AUFLIRA and AUFNIRA's nested files
are `(Array Int (Array Int Real))`, so they need a capability the IR does not
own — and a lane can attack that one today without touching `Sort`. The
remaining 7,530 (ALIA + ABV) need a third gate as well: `RowCtx::resolve_select`
(`abv.rs:2735`) has no arm for an array-valued base that is itself a `Select`.

**First decide rates for four divisions that had none**, over the 2,414 files in
them that parse today, at 24 s / 8 GiB / pinned core — and split BY FAMILY,
because a division's aggregate is evidence about its blocked set only when the
two come from the same generator:

    ABV  / UltimateAutomizer 2023   119 of 473  25.2%   <- 4,502 blocked files
    ALIA / UltimateAutomizer 2023     0 of  28   0.0%   <- 3,028 blocked files
    ALIA / piVC                       7 of  42  16.7%   <-     0 blocked files
    AUFLIRA, AUFNIRA / nasa, peter    no control exists  <- 19,620 blocked files

Quoting either aggregate would have been misleading in **both** directions:
AUFLIRA's climbs toward its `why` family (~61%, zero blocked files) and ALIA's
10.0% is entirely piVC (zero blocked files). Applying only the family-matched
rates puts the whole three-gate chain at **~1,135 files of 27,150 (4.2%)**,
essentially all of it one family of ABV — and that is still an over-estimate,
since the nested files are the harder half of every family.

**The design is settled even though it is not built.**
`ArraySortKey::Array(ArraySortId)` — intern the component key, not the sort —
leaves `Sort::Array { index, element }` and all ~170 field-binding sites
untouched and keeps `Sort: Copy`, which `Op`'s hash-consing key requires.
Measured cost: 514 `ArraySortKey` mentions across 75 files, 46 `.to_sort()`
sites. Rejected: `Sort::Array(ArraySortId)` (~170 pattern sites for recursion
nobody wanted) and front-end currying (front-end only, but 64.1% of ALIA /
50.6% of ABV / **0.0%** of AUFLIRA, whose files quantify over outer arrays).

**Next lane:** `!features.has_real` at `crates/axeyum-solver/src/auto.rs:6098`.
It gates 19,620 files, it is 2.6x the ALIA+ABV prize, and one flat query
demonstrates it.

<!-- plan-section: landed-changes -->

| 2026-09-13 | `825377a57` | `tests/nested_array_gate_map.rs`: the gate CHAIN behind the nested array sort, 7 tests, gated in `hooks/pre-push`. Three assert a capability we do NOT have and fail loudly when it arrives; the Int/Real pair is its own control. |
| 2026-09-13 | `665f86532` | The parse gate counted over all 29,564 files — 27,150 blocked, not 29,564 — with two independent instruments agreeing exactly, and the 2,414-file parse-ok control population pinned. |
| 2026-09-13 | `bfbd97dec` | Full-span 200-file parity lists for AUFLIRA / ABV / ALIA / AUFNIRA, committed before the first solve. Four divisions that had no list and no ledger row. |
