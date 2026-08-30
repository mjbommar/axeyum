# 345 — nursery draw 6

<!-- plan-section: lane-status -->

**Draw 6 is DECLINED, and that is the result.** ADR-0620 predicted it could
not satisfy R5 from un-owned modules; measured, it is worse — **zero**
coherent held-out-safe families exist, not one. Nothing was drawn:
`FAMILY_MODULES`, `FAMILY_ROUTES` and both manifests are untouched, no row
moved partition, no attestation count was raised, and `FROZEN UNCHANGED`
asserted directly with a negative control that fires.

R5 is hard-coded (`len(new_held_out) < 2` raises) and `PER_FAMILY = 10`, so
any draw needs **20 held-out-safe rows in two coherent families**. Of 2,155
drawable rows, 1,716 sit in modules an existing family already OWNS and are
unreachable; 11 un-owned modules reach the floor and **all 11 are over
mathematics a development or train family already publishes**. The un-owned
sub-floor remainder adjacent only to held-out is **7 rows spread over six
different questions** — not one family, let alone two.

Three corrections to ADR-0620, each re-derived here rather than carried
over ([ADR-0645](../../research/09-decisions/adr-0645-draw-6-is-declined-there-is-no-held-out-safe-family-left.md)):

1. **A third proposer/generator divergence**, beyond the two already
   recorded: the two scripts carry different `HYGIENE` regexes. The
   generator also drops `.inj`/`.injEq`/`.noConfusion` and
   `Int.Linear.*`/`Nat.Linear.*`, collapsing `Init.Data.Int.Basic` 10 → **6**
   and `Init.Data.Int.Linear` 10 → **2**. The first is the only un-owned
   floor-height module whose mathematics is unpublished, so under the
   proposer's screen it looks exactly like the held-out family this draw
   needed. **The drawable ready set is 11**, not the proposer's 15 and not
   ADR-0620's 13.
2. **`instSubNat` opens nothing for blind breadth** — 285 extra drawable
   rows and **0** new un-owned ready modules — though ADR-0620 names it the
   cheapest route. It stays the right lever for dispatchable rows.
3. **`Nat.dist` and `Nat.nth` are the unblock.** They open
   `Mathlib.Data.Nat.Dist` (**18** rows, a metric on ℕ, no family names
   `dist`) and `Mathlib.Data.Nat.Nth` (**11**, the k-th satisfying index,
   none mentioning `Prime`) — exactly the two held-out families R5 demands.
   R9 name screen 0/18 and 0/11.

**Also blocking the next draw:** `mathlib-statable-vocabulary-v1.json` has
two writers. `gen-autogenesis-nursery-refill.py --check` has been RED on
`main` since 04:23 today, and its own advice — "regenerate without
`--check`" — would delete `bridge_provenance` and `row_digest` inside a
commit that looks like a draw. I did not run it that way.

Gates: holdout isolation `held_out=116 settled=0 references=0 PASS` exit 0,
unchanged; frontier exit 0, dispatchable **12**, byte-identical before and
after; `validate-facts.py` 2,220 facts, 0 errors, exit 0.

Detail, all measurements and both screens' numbers:
[`../notes/345-nursery-draw-6.md`](../notes/345-nursery-draw-6.md).
