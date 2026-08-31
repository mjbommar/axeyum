# pareto-position — re-measure the cost model doc

<!-- plan-section: lane-status -->

**Status: DONE.** Audit/correction task, not a build task. No fact was
reclassified, reopened, or edited.

## The answer

`docs/formalized-math-2026-08/07-the-cost-model-and-pareto-position.md`
(2026-08-27) holds up in substance. Re-measured every checkable claim in it
against local `main` (see [ADR-1165](../../research/09-decisions/adr-1165-the-cost-model-re-measured-two-gates-moved-one-stayed-flat.md)
for full method and numbers) and corrected the document in place, following
doc 08's convention: dated blocks, old text struck through or quoted rather
than deleted.

Three things moved since 2026-08-27:

- **Congruence producer (§3): built.** `creal/congruence.rs` landed the same
  day doc 07 called it "waiting to be written" (`cb8b54e20`). One production
  consumer (`CReal.mulPowCongr`); nothing existing retired (the base
  congruences it depends on can't be re-derived through it without
  circularity).
- **Sharding gate (§4.3): closed** for the mechanism named. `creal_tests.rs`'s
  single pinned array is gone, replaced by 46 per-module shards under
  `creal/inventory/`. No cross-lane-conflict-rate tracking doc exists to
  quote a before/after number from, but the collision mechanism itself no
  longer exists.
- **Retrieval gate (§4.2): machinery built, gate not closed.** `shape_search`
  (ADR-0608, same day as doc 07) delivers the "must become machinery, not
  habit" ask. `scripts/brief-step0.py` (2026-08-29) measured why it hasn't
  closed the problem: used at brief time **4.8%** of the time over 272 lane
  status docs, against **46%** for mutation testing (which has both a harness
  and a CI gate). Two more retrieval-failure instances are dated after the
  tool landed (2026-08-29, 2026-08-30, both in CLAUDE.md).

One thing unchanged:

- **Contracts gate (§4.1): still 0 admissible.** `fact-frontier.py --json`:
  170 ready, 0 admissible, 1 declined. Producer-contract registry holds
  exactly two contracts; exactly one ready fact matches either — and is
  declined.

Re-verified and left alone: §1-2's strategy framing, every named example in
§3's "templates compound" item, the axiom-ledger pair (`total=30, axreal=30`,
every other prelude 0), and that doc 07 never overclaims the IVT/EVT worked
example (doc 08) beyond what it currently states.

**Could not verify**: the falsifiability paragraph's "~8.5 s incremental
degree-2 `∀x` identity / ~1 s concrete / ~356 s" triple — could not trace it
to a specific re-runnable benchmark in bounded time. Flagged as unverified
(not deleted, not silently re-asserted) in both the doc and the ADR. A
different, adjacent cost curve (Sturm isolation for the EVT decidable
fragment, degree 22-24) is separately measured and scales gracefully, but is
not a substitute for that specific axis.

## Commands run (all this lane's own worktree, local `main`)

```sh
python3 scripts/fact-frontier.py --json          # 170 ready / 0 admissible
python3 scripts/validate-facts.py                # route split, cas-certificate caveat
python3 scripts/gen-lean-axiom-ledger.py --check # total=30 axreal=30, rest 0
python3 scripts/gen-adr-index.py --check         # 707 rows, duplicates unchanged (0166/0167 grandfathered)
./scripts/check-links.sh                         # green
```

<!-- plan-section: landed-changes -->

| 2026-08-31 | (this lane) | Re-measured and corrected `07-the-cost-model-and-pareto-position.md` in place (dated correction blocks, doc-08 convention); added ADR-1165 with full method and numbers. |
