# Lane: nat-bitwise-facts — triage the 19 open `natural-bitwise` facts

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, nat-bitwise-facts, 2026-08-29).** Full triage of
all 19 `natural-bitwise` facts (per `nursery-v1.json`'s `family` field, which
is the authoritative 19 — `check-development-partition.py` and the
2026-08-27 curriculum doc both cite 19 for this family). **Zero facts closed**
— every one of the 18 real targets needs either a file outside this lane's
scope (`bitwise.rs`, owned by a sibling Opus lane right now; `binary.rs`,
never granted) or the fuel-irrelevance/bit-peeling machinery the CLAUDE.md
brief explicitly says not to duplicate. The 19th is a flagged MUTATION,
skipped per instructions. No `nat_prelude` source file was touched;
`nat_prelude` D+T count is unchanged at 85+432 (pinned in
`nat_prelude_tests.rs::the_build_is_deterministic`) before and after.

**Triage table (all 19):**

Detail moved to [`../notes/235-nat-bitwise-facts.md`](../notes/235-nat-bitwise-facts.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-bitwise-facts | full triage of all 19 `natural-bitwise` facts; 0 closed (all blocked on out-of-scope files or shared missing machinery, or are mirror mismatches, or a flagged mutation); no source changed |
