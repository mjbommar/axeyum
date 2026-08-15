# Lane: lean-ledger — the published axiom count, and why it was wrong

<!-- plan-section: lane-status -->

**The Lean axiom ledger published 65 trusted assumptions against an actual 32,
and now no count in it is authored** (`WIP`, lean-ledger, 2026-08-15). Decision:
[ADR-0465](../../research/09-decisions/adr-0465-the-axiom-ledger-is-derived-not-transcribed.md),
superseding
[ADR-0388](../../research/09-decisions/adr-0388-retain-axiomatized-int-and-use-nat-deficits-for-rado.md).

**Measured, not copied.** `real 30`, `integer 1`, `string 1` = **32**;
`nat 0` and `logic 0`, enumerated rather than inferred from an empty result;
119 Nat theorems; `int_theorem_inventory` 51 derived, 51 with an empty
`axiom_footprint`, 1 still asserted (`Int.euclidean_decomposition`). `real: 30`
is asserted **by design** (ADR-0456: an ordered commutative ring with 1), so a
blanket "axiom-free" assertion would be wrong and every expectation here is
per-prelude.

**ADR-0388 did bind.** Clause 1: *"Every result whose checked dependency closure
touches `build_int_prelude` states that it relies on 34 assumptions."* Clause 2:
*"The 34-row integer population remains in the generated axiom ledger."* Both
are now false about this repository, in the direction that understates it —
ℤ was constructed over the proved ℕ development (`229cceb1e` 34→6,
`0fc7cc357` 6→1) and the disclosure rule did not move, because it was written as
a constant. ADR-0465 supersedes the number and re-accepts the Nat-only Rado
boundary verbatim.

**The deliverable is the mechanism, not the number.** Ten documents were stale,
so fixing ten documents was never the fix.

- **No count survives in the tooling.** `EXPECTED_COUNTS`, the two `65` row
  assertions, the trust-policy literal `34`, the rendered prose, the unit test's
  literals, and the Rust `assert_eq!(…, 30/1/1)` are all gone. The manifest's
  `measurement` and `trust_policy` blocks — including the *publication rule
  sentence* — are composed from the measurement and re-derived by `--check`.
- **A zero cannot masquerade as absence.** An axiom-free prelude emits no rows,
  so the ledger now also consumes `nat_axiom_inventory`, which enumerates five
  preludes and prints a coverage line for each. The manifest records the prelude
  set, so a prelude dropping out of the measurement fails rather than shrinking
  the total.
- **The two enumerations police each other.** Per-prelude axiom counts, name
  sets, and canonical types must agree byte-for-byte, so an `Axiom`-only versus
  full-trusted-surface filter bug surfaces as a disagreement.
- **A reduction is published as a reduction.** `--check` fails on any population
  change; clearing it needs `--accept-population-change` with a date, a reason
  and existing evidence, which files the departed rows in `retired_entries`
  rather than deleting them. The 33 discharged integer rows are in the generated
  ledger with their type digests, not erased.
- **Documents that cite the counts are gated.** Ten are declared in
  `live_documents` and scanned against a closed family of anchored phrasings —
  and each must yield **at least one** match, so deleting the sentence is a
  failure rather than the cheapest way to pass.

**Every control was exercised, not asserted.** Nine negative controls fire:
three end-to-end through the real kernel (a prelude dropped from the row
inventory → *"the two inventories disagree on real: … 0 axiom rows … declared
axiom=30"*; a renamed axiom → *"the two inventories name different axioms"*; a
stale/absent citation in a live document → exit 1), and the rest as 24 unit
tests that mutate a captured measurement so they need no rebuild. Two drafted
scan patterns matched nothing anywhere and were **deleted**, because a dead
pattern gates nothing while looking like coverage — the liveness test found them.

**Gates.** `cargo test -p axeyum-lean-kernel` green (276 lib + every integration
suite), clippy `-D warnings` clean, `check-lean-gate.sh` **122 real-Lean checks
(floor 111)**, `validate-facts.py`, `check-links.sh`, `gen-adr-index --check`,
`gen-lean-axiom-ledger --check`, 24/24 ledger contract tests. All run in a
`lane-snapshot.sh` tree: the worktree carries another lane's in-progress
`tc.rs`/`inductive.rs`, which fails `k_like_reduction` and clippy on an untracked
test — reproduced as **not mine** by running clean `HEAD` (7/7 green).

**Not done, deliberately.** `scripts/check-aggregate-scope.sh` still says
"all 65 prelude axiom types" inside a dated 2026-08-14 measurement narrative;
correcting a historical record would falsify it. Dated plan results, diaries and
superseded ADRs keep their numbers for the same reason. The scan's limit is
stated in the generated ledger and the ADR: it gates the *anchored* phrasings,
not every integer in a declared file.

**Next for this lane.** The 30 `real` rows are now 94% of the trusted surface
and the obvious target; ADR-0456 already names the trigger for building ℚ.
Nothing else in the ledger is blocked.

<!-- plan-section: landed-changes -->

| 2026-08-15 | `dc1c299cf` | The Lean axiom ledger published **65** assumptions against an actual **32** (real 30, integer 1, string 1) — ADR-0388's 34-assumption disclosure rule outlived the construction of ℤ by two days because it was a constant. ADR-0465 supersedes it: counts are derived from two cross-checked measurements, one of which declares its own per-prelude coverage so an axiom-free prelude cannot read as unmeasured; population changes need an explicit `--accept-population-change` that files departed rows as retired rather than deleting them; and ten citing documents are scanned with a liveness requirement. Nine negative controls exercised, three end-to-end through the kernel. 33 discharged integer rows published as a reduction. |
