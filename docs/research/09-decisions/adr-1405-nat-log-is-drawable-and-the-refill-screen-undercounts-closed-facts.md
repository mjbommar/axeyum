# ADR-1405: `Mathlib.Data.Nat.Log` is drawable; the refill screen had two independent headroom-overstating gaps, both now fixed

Date: 2026-09-01
Status: Accepted
Lane: `screen-nat-log-family`

Index-summary: Screened `Mathlib.Data.Nat.Log` for drawability into the
nursery. Found and fixed TWO independent gaps in
`scripts/propose-nursery-refill.py`, both in the headroom-OVERSTATING
direction. (1) `used_source_names()` read only nursery draw manifests, never
the fact ledger, so a Mathlib mirror closed by direct flip (no nursery draw)
stayed "unused" forever — 20 of the tool's reported 37
`Mathlib.Data.Nat.Log` survivors already had a `proved` fact this way.
(2) The tool never applied the generator's `HELD_OUT_CONSTRUCTIONS` screen
at all (found by the coordinator, verified here against `nursery-v1.json`'s
`entries[].partition` directly), so a module whose every candidate mentions
a construction still guarding a blind v1 held-out family could read as
ready while `select()` would refuse it. Fixed both at the source:
`catalogued_source_names()` mirrors the real generator's `catalogued`
screen exactly, and `held_out_constructions()` mirrors
`HELD_OUT_CONSTRUCTIONS` by regex, same pattern as the existing
`read_pins()`. Made the substantive decision this unblocks: dropped
`Nat.log`/`Nat.clog` from `HELD_OUT_CONSTRUCTIONS` (`natural-logarithm` has
zero `held-out` rows, verified directly). **`Nat.log2` and `Nat.sqrt` both
stay** — `Nat.sqrt` because it is the only construction guarding
`natural-square-root` (the only v1 family with any `held-out` row), and
`Nat.log2` for a DIFFERENT, non-obvious reason found only by measuring
`select()`'s actual output rather than reasoning about topics: dropping it
alone (even though `natural-logarithm` does not need it either) displaces
`Nat.not_exists_sq` from an UNRELATED already-drawn HELD-OUT family
(`natural-elementary-bounds`)'s alphabetical top-10 slice in favour of
`Nat.log2_two`, which newly passes every other screen once `Nat.log2` is
un-excluded. That is exactly the retroactive blind-population alteration
ADR-0542's amendment discipline exists to prevent, and it would have
happened via silent regeneration rather than a reviewed amendment had it
not been measured with `select()` itself before landing (`{"Nat.log2",
"Nat.sqrt"}` against the original four-constant set: zero entry-set
difference across all 460 already-drawn rows, confirmed). Added a
mutation-tested control (`scripts/tests/mutation_controls.py`'s
`nursery-refill-headroom-screen` suite) that fails if either `Nat.sqrt` or
`Nat.log2` is ever dropped. Corrected, re-measured counts:
`Mathlib.Data.Nat.Log` 37 → **17**, `Mathlib.Data.Nat.Bitwise` 18 →
**dropped out of the ready-family list entirely** (< 10),
`Mathlib.NumberTheory.FactorisationProperties` unchanged at **15**.
`Mathlib.Data.Nat.Log` is drawable — all 17 open candidates `FLIPPABLE`, no
construction needed, R9-clean — but **cannot clear the frontier floor
alone**, a structural property of `dispatchable_yield()` independent of
survivor count (a solo new family always sends 100% to held-out). A draw
needs a second family; per this measurement the only other current
candidate is `Mathlib.NumberTheory.FactorisationProperties`, unscreened for
R9/R11 by this lane. Full detail:
[2026-09-01-screening-the-nat-log-family.md](../11-design-review/2026-09-01-screening-the-nat-log-family.md).
Renamed from ADR-1400 after a same-day collision with a sibling lane's ADR
of the same number.
Index-status: Accepted

## Context

`scripts/check-dispatchable-frontier.py` measured the dispatchable ml430
frontier down to 20 (floor 10) after this session's draws.
`scripts/propose-nursery-refill.py --remeasure` named three hygiene-clean
refill candidates — `Mathlib.Data.Nat.Log` (37), `Mathlib.Data.Nat.Bitwise`
(18), `Mathlib.NumberTheory.FactorisationProperties` (15) — explicitly
labeled an upper bound, not screened for R9 contamination or R11 adjacency
("draw 10 was DECLINED against this same shortlist"). Bitwise and
FactorisationProperties are contamination-exposed by other lanes' concurrent
work; `Nat.Log` was the one candidate no running lane touches, so this lane
screened it in isolation.

Per ADR-0653 (see the `natural-distance` incident this lane's brief cites): a
screening lane must not declare theorems whose names match Mathlib mirror
names in the family under review, because doing so spends the blind
evaluation population it is being sent to protect. This lane declared
nothing; every finding below is measurement, plus two tooling fixes the
coordinator explicitly authorized after independently verifying both gaps.

The tooling fixes happened in three passes, and the third is the reason
this ADR is worth reading past its summary. Pass one found the fact-ledger
gap (20 of 37) and, on the coordinator's original instruction, left the
tool itself unfixed ("this is a screening lane, not a tooling lane"). The
coordinator then (a) independently verified that finding and the
Mathlib-source correction below, (b) found the SECOND gap by reading
`gen-autogenesis-nursery-refill.py`'s own comment, and (c) explicitly
directed this lane to fix both gaps, drop `Nat.log`/`Nat.clog`/`Nat.log2`
from `HELD_OUT_CONSTRUCTIONS`, keep `Nat.sqrt`, and add a mutation-tested
control. Pass two implemented exactly that instruction and, before
committing, ran `scripts/gen-autogenesis-nursery-refill.py --check` as a
final sanity pass — which is what surfaced pass three: dropping `Nat.log2`
specifically (not `Nat.log`/`Nat.clog`) silently changes the ALREADY-DRAWN
`natural-elementary-bounds` held-out family's membership. Pass three is the
correction: `Nat.log2` stays, for a reason unrelated to why `Nat.sqrt`
stays.

## Decision

1. **Fix `propose-nursery-refill.py`'s fact-ledger blind spot.** Added
   `catalogued_source_names()`, which reads
   `mathlib-nat-int-fact-catalog-v1.json`'s `external-source` rows exactly
   the way the real generator's `select()` does (`catalogued =
   {row["source_name"] for row in catalog["facts"] if row["kind"] ==
   "external-source"}`) — matching the real screen rather than inventing a
   parallel rule that can drift from it, per the coordinator's explicit
   instruction. `used_source_names()` now unions it with the two nursery
   manifests it already read.

2. **Fix `propose-nursery-refill.py`'s `HELD_OUT_CONSTRUCTIONS` blind spot.**
   Added `held_out_constructions()`, reading the generator's
   `HELD_OUT_CONSTRUCTIONS` set by regex from its own source (the same
   pattern `read_pins()` already uses for `PER_FAMILY`/`PARTITION_CYCLE`/
   the inventory pin, so a future edit to the set cannot silently drift from
   what this screen enforces). Wired into both `remeasure()`'s per-record
   loop and `show_names()`, in the same relative order `select()` uses
   (after not-statable-here, before elided-proof-glyph).

3. **Make the `HELD_OUT_CONSTRUCTIONS` decision, in two measured steps, not
   one asserted one.** `gen-autogenesis-nursery-refill.py`'s
   `HELD_OUT_CONSTRUCTIONS` was `{"Nat.log", "Nat.clog", "Nat.log2",
   "Nat.sqrt"}`.

   **Step A — verify what a blind family actually needs.** Against
   `nursery-v1.json`'s `entries[].partition` directly, not against the
   generator's own comment or the coordinator's message:

   ```
   every natural-logarithm entry: partition == 'development'   (0 held-out)
   every natural-square-root entry: partition == 'held-out'    (all held-out)
   every v1 family with ANY held-out row, scanned across all of them:
       ['natural-square-root']
   ```

   So `natural-logarithm` has been fully spent into `development` since
   ADR-0542 (2026-08-30) and `natural-square-root` is the ONLY family with
   any `held-out` row — the last surviving v1 blind family, guarded solely
   by `Nat.sqrt`. This step alone suggested dropping all three of
   `Nat.log`/`Nat.clog`/`Nat.log2`.

   **Step B — verify the drop against `select()` itself, not against the
   topic argument.** Built a read-only diagnostic that calls the real
   `select()` with the ORIGINAL four-constant set and with each candidate
   reduced set, and diffed the resulting `(family, source_name)` pairs
   directly — never trusting that "no family needs this constant's TOPIC"
   implies "removing it changes nothing". Result:

   ```
   drop {"Nat.log","Nat.clog"} only, keep {"Nat.log2","Nat.sqrt"}: ZERO diff
   drop "Nat.log2" alone (any other set kept): NOT zero --
       + natural-elementary-bounds: Nat.log2_two
       - natural-elementary-bounds: Nat.not_exists_sq
   ```

   `natural-elementary-bounds` is an ALREADY-DRAWN family, unrelated to
   `Nat.log`/`Nat.clog`/`Nat.log2` by topic, and independently confirmed
   `held-out` in all 10 of its `nursery-v2-extension.json` rows. Dropping
   `Nat.log2` admits `Nat.log2_two` (which mentions `Nat.log2`) past every
   other screen, and it sorts alphabetically ahead of `Nat.not_exists_sq`
   in that family's `pool[:PER_FAMILY]` slice — displacing a member of a
   BLIND family via a constant edit whose stated justification was about a
   DIFFERENT family entirely. This is exactly the retroactive alteration
   ADR-0542 exists to prevent, and it would have shipped silently: `select()`
   is deterministic and re-derives the manifest whole on every regeneration,
   so nothing marks a member as "was already drawn, do not reshuffle" at
   this granularity.

   **Landed:** `HELD_OUT_CONSTRUCTIONS = {"Nat.log2", "Nat.sqrt"}` — dropped
   only `Nat.log` and `Nat.clog`, confirmed zero-diff against the original
   set over all 460 rows `select()` currently produces (re-verified after
   landing, not merely predicted).

4. **Add a mutation-tested control on both surviving constants,** per the
   coordinator's explicit statement that this control matters more than the
   removal itself. `scripts/tests/test_propose_nursery_refill.py`'s
   `HeldOutConstructionsTests` asserts `held_out_constructions() ==
   {"Nat.log2", "Nat.sqrt"}`, and separately that `Nat.log`/`Nat.clog` are
   absent (protection against an accidental re-add in the other direction).
   Registered in `scripts/tests/mutation_controls.py`'s new
   `nursery-refill-headroom-screen` suite, with a mutation changing the
   generator's `HELD_OUT_CONSTRUCTIONS = {"Nat.log2", "Nat.sqrt"}` to
   `{"Nat.evil"}`. Run through the real harness, not a hand-rolled loop:

   ```
   $ python3 scripts/tests/mutation_controls.py nursery-refill-headroom-screen
   nursery-refill-headroom-screen: baseline green, 7 tests
     a fact-catalog name (drawn or flipped directly) is not headroom killed 1: test_a_proved_fact_never_drawn_through_the_nursery_is_excluded
     Nat.sqrt and Nat.log2 must stay in HELD_OUT_CONSTRUCTIONS ... killed 3: test_mirrors_the_generators_set, test_nat_log2_is_present, test_nat_sqrt_is_present
   ```

   Exit 0 — both mutations are `killed N`, confirming the controls genuinely
   fail without their respective fixes.

5. **Treat `Mathlib.Data.Nat.Log` as drawable**, with the true open-candidate
   count corrected to **17** (not 37, and unaffected by the final
   `HELD_OUT_CONSTRUCTIONS` decision — re-measured after landing `{"Nat.log2",
   "Nat.sqrt"}`, still 17: none of the 17 open `Nat.log`/`Nat.clog`
   candidates mention `Nat.log2` as a type constant). All 17 are plain
   value-level facts, reachable from existing kernel machinery
   (`log_aux_mono`, `log_aux_le_fuel`, `log_aux_antitone_base`,
   `clog_aux_mono`, `clog_aux_antitone_base`, `log_aux_le_clog_aux`, all
   already declared in `crates/axeyum-lean-kernel/src/nat_prelude/
   log_clog_order.rs`). No construction work is needed to unblock this
   family, unlike `Nat.dist`/`Nat.nth` (ADR-0653) — `Nat.log`, `Nat.logAux`,
   `Nat.clog`, `Nat.clogAux`, `Nat.log2` are already declared and proved
   axiom-free.

6. **`Mathlib.Data.Nat.Log` cannot clear the frontier floor alone**, and this
   is independent of its survivor count. `dispatchable_yield(n) =
   PER_FAMILY * (n - ceil(n / PARTITION_CYCLE_LEN))`: at `n = 1`,
   `ceil(1/3) = 1`, so a solo new family sends 100% of itself to held-out and
   yields 0 dispatchable rows regardless of how many candidates it has. A
   draw needs a second new family; re-measured with both fixes applied, the
   only other module currently reporting `>= PER_FAMILY` survivors is
   `Mathlib.NumberTheory.FactorisationProperties` (15) —
   `Mathlib.Data.Nat.Bitwise` (previously 18) dropped out of the ready-family
   list entirely once the fact-ledger fix applied, almost certainly because
   a concurrent lane (`nat-size-squarefree`) is actively flipping bitwise
   mirrors directly. Neither the pairing's R9/R11 cleanliness nor
   `FactorisationProperties`'s exact per-statement verdicts were screened by
   this lane.

## Consequences

- A draw author can add `"natural-logarithm": ("Mathlib.Data.Nat.Log",)` to
  `FAMILY_MODULES` and `("kernel-induction",
  "recursive-function-reconstruction")` to `FAMILY_ROUTES` and the module
  will no longer hit the `RefillError` it would have hit before this ADR
  (`held-out-construction` no longer excludes `Nat.log`/`Nat.clog`
  candidates). Still needs a second family (see point 6) and the real
  `select()`/`guard()` (R1–R11) run to confirm R9/R11 — this ADR predicts R9
  clean and the first-10 alphabetical slice by reading the generator's
  logic, but does not run it.
- `propose-nursery-refill.py`'s reported counts for EVERY module, not just
  `Mathlib.Data.Nat.Log`, are now closer to what `select()` would actually
  draw. `Mathlib.Data.Nat.Bitwise` dropping from the ready list under the
  fixed screen is the clearest evidence the fix has real effect beyond the
  one family this ADR was scoped to.
- `gen-autogenesis-nursery-refill.py --check` was run (read-only reproduction
  against the CURRENT `FAMILY_MODULES`, which this ADR did not touch) to
  confirm the `HELD_OUT_CONSTRUCTIONS` edit does not silently perturb any
  already-drawn family; it reported the extension file byte-different only
  in its own `screens.held_out_constructions` provenance field and
  `extension_sha256` (confirmed via diff: zero `entries` difference), so the
  generator was run once, without `--check`, to bring that provenance field
  current. No new family, no changed partition, no changed member.
- The screening report still flags (but does not fix) a stale doc-comment
  claim in three `nat_prelude` source files about Mathlib's `Nat.log`/
  `Nat.clog` recursion shape — unaffected by this update, which touched only
  `scripts/propose-nursery-refill.py`, `scripts/gen-autogenesis-nursery-refill.py`,
  their test suites, and `artifacts/autogenesis/{refill-headroom-v1,nursery-v2-extension}.json`.
  A follow-up lane not mid-screen should still correct the doc comments.

## Alternatives considered

- **Trust the 37 as reported and hand it to a draw author unscreened.**
  Rejected: the brief this lane was given explicitly required verifying the
  candidate list against the tree rather than treating a headline number as
  fact. The cross-check found a 54% overcount within the first hour of work.
- **Leave `used_source_names()` unfixed, as a screening lane rather than a
  tooling lane.** This was the ORIGINAL decision in this ADR's first
  version. Superseded: the coordinator independently verified the finding,
  found a second structurally identical gap, and explicitly directed the
  fix plus a mutation-tested control — at which point declining to fix it
  would have been declining a direct, scoped instruction, not preserving a
  lane boundary. The fix touches only two well-isolated functions plus one
  constant; it does not touch `FAMILY_MODULES`/`FAMILY_ROUTES`, so it is not
  authoring a draw.
- **Drop all three of `Nat.log`/`Nat.clog`/`Nat.log2` from
  `HELD_OUT_CONSTRUCTIONS`, as the coordinator's instruction literally
  read.** This was landed, then REVERTED for `Nat.log2` specifically, before
  this ADR's final commit — see Decision point 3, Step B. The instinct that
  motivated it ("no blind family's TOPIC needs any of the three") was
  correct and insufficient: it does not account for an unrelated family
  whose alphabetical draw slice happens to be adjacent to what the drop
  admits. Caught only by running `select()` itself and diffing, not by
  reasoning further about topics.
- **Apply a `proved`-status filter to `catalogued_source_names()`, narrower
  than the real generator's `select()`.** Rejected per explicit instruction:
  match `select()`'s actual screen (any `external-source` row, proved or
  not) rather than inventing a second rule that can drift from it. The real
  generator does not distinguish, and neither does this fix.
- **Guard `Nat.sqrt`/`Nat.log2` with a module-level `raise` on import instead
  of a test.** Considered and rejected: `test_gen_autogenesis_nursery_refill.py`
  and the new `test_propose_nursery_refill.py` both `exec_module` the
  subject at import time, so a raising guard would abort every OTHER
  mutation's test collection for the same subject file too, and the
  mutation harness would classify that as `DID NOT BUILD` — not a
  measurement, per its own documented semantics. A normal test assertion,
  registered in `mutation_controls.py`, gives a clean `killed N` instead.
