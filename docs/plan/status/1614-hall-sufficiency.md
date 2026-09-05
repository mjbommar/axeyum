# Lane: hall-sufficiency — the two-dimensional subset search, and where Hall now stands

<!-- plan-section: lane-status -->

**Your lane's block (`landed`, hall-sufficiency, 2026-09-04).** ADR-1608 stopped
Hall's marriage theorem at *necessity* and named the obstruction: with no
classical choice the critical subfamily must be **computed**, by a bounded
search over the subsets of a `Nat.Finset` with a reflection lemma reading the
verdict back into the kernel. That primitive now exists
([ADR-1614](../../research/09-decisions/adr-1614-searching-over-subsets-is-a-reflection-primitive-not-a-hall-detail.md)),
together with `Nat.strongInduction` — ADR-1608's item 1, also measured absent.

Thirteen declarations, empty axiom footprint, `nat_prelude::` green:

- `Nat.Finset.bitB`/`decode`/`encodeFrom`/`encode`/`anySubset` — the
  enumeration. `Nat.testBit` **already existed** (`--name-like testBit` returns
  FOUND 15 while `decode`, `encode`, `subsets`, `powerset`, `enumerate` and
  `bitAt` all return ABSENT), so searching for the STEP rather than the NAME
  removed a bit decoder from the diff.
- `Nat.Finset.existsSubset_of_search` / `forallSubset_of_search` — the
  reflection lemma in both polarities, the two-dimensional twin of
  `allBelow_false_witness` / `allBelow_true_at`. Each is the other's negative
  control at the trusted gate.
- `Nat.Finset.memB_decode_encode` — exhaustiveness, at EVERY index, not only
  below the width.
- `Nat.Finset.card_congr_of_memB` — in `finset.rs`, not beside its consumer:
  two sets with the same members have the same `card` even when their stored
  bounds differ. This is what discharges `forallSubset_of_search`'s congruence
  premise for a `card`-based property.
- `Nat.strongInduction.{u}` and `strongInduction_eq` over `lt_well_founded` +
  `WellFounded.fix`/`fix_eq`.

**Hall's sufficiency did NOT land, and the obstruction has MOVED.** ADR-1608's
items 1 and 2 are closed; item 3 is not, and building item 2 sharpened what
item 3 costs. The choice problem is solved; the **counting** problem is not:

1. `Nat.Hall.unionOver` has no congruence lemma — its bound reads `t`'s stored
   bound, not `t`'s members, so two membership-equal index sets give unions with
   different bounds and nothing relates their memberships. Needs `anyBelow`'s
   *elimination* rule, which is now a one-dimensional instance of
   `allBelow_false_witness`. Bookkeeping.
2. **Transporting `HallCondition` across a deleted family** —
   `fun i => sdiff (nb i) (unionOver nb t)` — is a genuine counting argument
   over a union whose bound changes at every step. This is the real remaining
   work.
3. Gluing two matchings needs their images disjoint;
   `Nat.Finset.card_le_of_injOn` is the right tool and exists, but nothing
   relates the two images yet.

A lane taking the next slice should **not** size the search again — it should
size `unionOver` under family modification and expect that to be the whole of it.

<!-- plan-section: landed-changes -->

| 2026-09-04 | hall-sufficiency | subset-search reflection primitive + `Nat.strongInduction` + `card_congr_of_memB`; Hall sufficiency still open, obstruction re-sized (ADR-1614) |
