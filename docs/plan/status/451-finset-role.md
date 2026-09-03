# Lane: finset-role — a computed `Nat.Finset` carrier (predicate + bound)

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, finset-role, 2026-09-03).** `Nat.Finset` landed
(`nat_prelude/finset.rs`, ADR-1577): a one-constructor inductive
`mk : (Nat → Bool) → Nat → Finset`, with `memB` truncating inside its own
definition, `card s := countRange (memB s) (bound s)` and
`sum s f := sumRangeIf (memB s) f (bound s)`. **Twelve theorems, every one
admitted on the first attempt, every one with `Kernel::axiom_footprint = []`**
read from `theorem_axiom_footprint`. No quotient, no `propext`, no `List`, ℕ
only — ADR-1520's `Nat.Multiset` shape applied to sets. `nat_prelude::` suite
422 passed / 0 failed; clippy clean on the crate.

**The one thing that did NOT land is the pigeonhole principle, and the
obstruction is measured rather than guessed.** A pigeonhole over two
`Nat.Finset`s needs `countRange p n ≤ countRange q m` from an INJECTION between
two selected sets, and that lemma is absent:
`shape_search --hyp Nat.injectiveOn --concl Nat.le` returns ABSENT on a freshly
built binary (`declarations=3095`, positive control `Rat.rank_eq_rankCols`
`FOUND 2`, namespace control `ns Nat=1088`). `Nat.pigeonhole` DOES exist but is
the RANGE form — domain `[0,n)`, codomain `[0,m)` — and bridging it needs an
ENUMERATION of a finite set's members as `[0, card s)`, which
`--name-like nthtrue / enumerate / rankof` reports absent as well. Sizing for
the next lane is in ADR-1577: an induction on the domain's bound that peels one
member and removes its image, so it needs a "removing one member decreases
`countRange` by exactly one" step; `Nat.countRange_point_change` is the closest
existing piece. It is comparable in size to everything else in the ADR put
together, which is why it was not attempted rather than attempted badly.

**A second finding, about the tree rather than this lane.** The brief asked for
an existing ad-hoc-`countRange` proof to be REWRITTEN through the carrier. I
surveyed and found no site where the substitution makes an existing proof
shorter: every one already has the predicate-level algebra it needs, because
`finite_set.rs` landed `setUnion`/`setInter`/`setDiff`/`Subset` with their
counting laws first. What was missing was not a shorter proof but an OBJECT. So
the consumer is a bridge — `Nat.Finset.card_totatives` proves that
`Nat.totient`'s defining ad hoc `countRange` IS a `Finset` cardinality, with
`Nat.totient` and everything proved about it unchanged.

Reused rather than rebuilt, and the carrier is thin on purpose:
`Nat.countRange` with `countRange_split` / `countRange_congr_lt` /
`countRange_eq_zero_of_all_false` / `countRange_union_add_inter` /
`countRange_le_of_subset`, `Nat.setUnion`/`setInter`/`setDiff` and `Nat.Subset`
(`finite_set.rs`), `Nat.sumRangeIf` with `sumRangeIf_congr_lt`
(`subset_sum.rs`), and `Nat.sumRange_split`/`sumRange_add`/`sumRange_const_zero`.

Eight facts registered, one per distinct statement, all `proved` with empty
`axiom_footprint`. Both ledger checkers were **verified to fail before being
written**: the kernel-term row greps a distinguishing substring of the TYPE (the
same pattern with `union`/`inter` transposed hits zero), and the footprint row
pins the name AND the size with `awk` on tab fields (a one-character name typo
hits zero; asking for size 1 hits zero). `validate-facts.py` then rejected the
first draft — it DERIVES dependencies from the proof term and found nine edges
the hand-written `depends_on` lists had missed.

**One hand-computed expectation was wrong and the evaluation test caught it**:
the first draft asserted `bound {0,1,2} = 9`, but `union` takes the SUM of its
operands' bounds, so it is `(1 + 2) + 3 = 6`.

**Nothing did-not-run.** Every gate quoted above was executed in this worktree
and its output read.

<!-- plan-section: landed-changes -->

| 2026-09-03 | finset-role | `Nat.Finset` carrier + inclusion–exclusion (`464b9cce9`) |
| 2026-09-03 | finset-role | bounded-loop reflection + `card_le_of_subsetB` (`1d6da1db6`) |
| 2026-09-03 | finset-role | `sum_union_disjoint` and its sum workhorse (`22568ec44`) |
| 2026-09-03 | finset-role | `sum_congr_of_beq` (`75d72dcec`) |
| 2026-09-03 | finset-role | consumer: `card_totatives` identifies the totient (`cfd85cf1a`) |
| 2026-09-03 | finset-role | eight facts, checkers verified to fail when perturbed (`3b53ee52e`) |
| 2026-09-03 | finset-role | ADR-1577, regenerated ADR index and py prelude fields |
