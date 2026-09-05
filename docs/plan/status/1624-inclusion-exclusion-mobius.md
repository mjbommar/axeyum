# Lane: inclusion-exclusion-mobius — the subset-indexed sum, and W2-19 on top of it

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, inclusion-exclusion-mobius, 2026-09-05).**
Roadmap **W2-19** (general inclusion–exclusion) LANDED. The reusable primitive
underneath it — a sum indexed by subsets, with a `refl` split law — landed
first. Möbius inversion did NOT land and the remaining obstruction is smaller
and named. Decision record: [ADR-1624](../../research/09-decisions/adr-1624-a-subset-is-a-predicate-because-the-split-law-has-to-be-refl.md).

**The design decision, because it is the reusable part.** A subset here is a
`Nat → Bool` **predicate** and the enumeration is a fold over the WIDTH, so

```text
sumSubsets (succ n) F = sumSubsets n F + sumSubsets n (fun s => F (insertAt n s))
```

is `Eq.refl`. ADR-1614's `Nat.Finset.decode` enumerates the same `2^n` subsets
by a bit code; over THAT enumeration the same law has to split `[0, 2^(n+1))`
at `2^n` and then prove `testBit (2^n + k) i = testBit k i` below `n` and
`testBit (2^n + k) n = 1` — a `div`/`mod`-by-`2^i` development this prelude does
not have. Over a `Nat.Finset` the law cannot be `refl` at all: the carrier
stores a bound, so `decode n k` and `decode (succ n) k` are different terms for
the same set. ADR-1619 proposed the code shape for this slice; this lane
rejected it and the ADR records why.

**What landed.** Forty-one declarations, every axiom footprint empty (fourteen
definitions, twenty-seven theorems — the whole `Nat.Subsets` namespace as
`nat_theorem_inventory Subsets.` reports it):

- `nat_prelude/subset_sums.rs` — `sumSubsets`/`sumSel`/`sumSelPos`, both split
  laws, `Supported` and `sumSel_congr` (the support obligation, stated rather
  than hidden), `sumSel_add`/`sumSel_mul_right`/`sumSel_swap`, the two
  `sumSelPos` bridges, `sumSubsets_card` (`= pow 2 n`) and `sumSel_const` — the
  alternating sum over a non-empty ground set vanishes, whose whole proof term
  is `Nat.add_comm`.
- `nat_prelude/inclusion_exclusion.rs` — `Nat.Subsets.inclusion_exclusion`,
  `inclusion_exclusion_pos` (the classical form, over the non-empty
  subfamilies), and `inclusion_exclusion_two`, which is
  `Nat.countRange_union_add_inter`'s statement derived from the general result
  at `n = 2`. The test builds that statement once and offers it to the trusted
  gate TWICE — with the derived theorem and with the pre-existing lemma applied
  at `A 0`, `A 1` — so "the two-set case is recovered" is the kernel accepting
  the old lemma at the new statement, not two rendered types that look alike.

**What did NOT land, precisely.**

1. **Möbius inversion.** ADR-1619 named the missing bijection: for squarefree
   `n`, the divisors are the products of the SUBSETS of its prime factors. The
   *alternating sum* half of that argument is now one line (`sumSel_const`).
   The **bijection** is not, and nothing here shortens it — it needs
   `Nat.factorization` as a multiset, a product over a sub-multiset, and
   injectivity from unique factorisation. Nothing indexes a multiset by a
   `Nat → Bool` predicate, which is the join it needs. Do not read W2-19 as
   unblocking Möbius.
2. **`Nat.dirichlet_assoc` is still ABSENT** (checked at the start of the lane:
   `arith_functions_family.rs` declares `dirichlet` and `dirichlet_comm` and no
   associativity). It was not attempted, because item 1 blocks the theorem it
   would serve.
3. **The two subset enumerations are not related by any theorem.** `decode` and
   `sumSubsets` range over the same subsets in the same binary order — the count
   is pinned by `sumSubsets_card` and the order by the tests at `n ≤ 3` — but no
   declaration says so, and the bridge costs exactly the `testBit (2^n + k)`
   development that was avoided.
4. **Inclusion–exclusion is stated over predicates, not `Nat.Finset`s.** That is
   what makes the two-set case `countRange_union_add_inter`. A `Finset` wrapper
   needs `card_eq_countRange_add` to reconcile per-set bounds against a common
   ambient range; mechanical, not built.

**Mutation, measured.** Two mutants were RUN, both killed by the trusted gate.
The uncoordinated parity flip (`sumSel`'s base branches exchanged) dies at step
`equations`. The COORDINATED five-edit version — definition, `sumSel_zero`'s
statement, and both `sumSelPos` bridges' parities — dies two steps EARLIER than
predicted, at `sumSel_congr`, whose base case transports through the context
`fun x => bool_select_nat b x 0` and so pins the parity convention inside a
proof term rather than in the equation that states it. **No mutant the kernel
admits was constructed**, so this lane does not claim its evaluation tests are
load-bearing; they are the readable pin. One real correction came out of the
exercise: `sumSubsets_card` does NOT pin that the two halves are different (a
fold reading `ih F + ih F` satisfies `= pow 2 n` too), and the doc comment that
said it did was fixed.

**Gates.** `nat_prelude::` 602 passed / 0 failed (`--release --test-threads=4`);
`cargo check --workspace --all-targets` clean (run because a `NatPrelude` field
addition breaks the generated consumer in `axeyum-py`;
`gen-py-prelude-fields.py` regenerated, `nat` 1234+113 → 1252+113);
`validate-facts.py` 2820 facts / 0 errors after
`check-fact-depends-derived.py --fix` added four edges the proof terms already
carried; `clippy -p axeyum-lean-kernel --all-targets -D warnings` exit 0;
`cargo fmt --all --check` exit 0; `check-links.sh` all links ok;
`check-merge-hygiene.sh` PASS (after regenerating the production-provenance
ledger and rebuilding `shape_search`, both of which it reported stale).

**Projection, base against head.** `kernel_declaration_projection` was built at
the lane's base commit in a `lane-snapshot.sh` copy and again at the lane head,
and the two outputs diffed: **0 rows removed, 492 rows added, 41 DISTINCT
declaration names added, every one of them under `Nat.Subsets.`**. The 492 is
41 x the 12 prelude labels the projection emits a row under, and the 41 is the
same number `shape_search` reports as the difference between
`declarations=3000` at the base and `declarations=3041` at the head — two
independent counts of the addition, neither taken from the diff. The positive
control for the base measurement was `--name Nat.sumDivisorsBy_reindex
--expect 1` FOUND, exit 0.

<!-- plan-section: landed-changes -->

| 2026-09-05 | inclusion-exclusion-mobius | `Nat.Subsets.sumSubsets`/`sumSel` and a `refl` split law: a subset is a `Nat → Bool` predicate, not a `Nat.Finset`, so the split costs nothing (ADR-1624) |
| 2026-09-05 | inclusion-exclusion-mobius | W2-19 general inclusion–exclusion as two `Nat` sums, with the two-set case derived and checked against `Nat.countRange_union_add_inter` verbatim |
| 2026-09-05 | inclusion-exclusion-mobius | Möbius inversion did NOT land; the missing bijection (divisors of a squarefree `n` ↔ subsets of its prime multiset) is sized, and `Nat.dirichlet_assoc` is still absent |
