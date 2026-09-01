# Lane: int-sumrange

<!-- plan-section: lane-status -->

**Status:** landed. `Int.sumRange` and eight lemmas exist, all admitted by the
trusted gate on the first attempt, all `axiom_footprint` 0. ADR-1260's named
obstruction between the lattice-point partition and Eisenstein's lemma is gone.

Decision and mutation table: [ADR-1275](../../research/09-decisions/adr-1275-int-sumrange-lands-and-two-of-prods-lemmas-do-not-transport.md).

## What landed

`crates/axeyum-lean-kernel/src/int_prelude/sum.rs` (new, ~830 lines):

- `Int.sumRange` — `Nat.rec` over the bound, exclusive, `Int.zero` base, fresh
  term on the right, matching `Nat.sumRange` and `Int.prodRange`.
- `Int.sumRange_zero`, `Int.sumRange_succ` — both `Eq.refl`.
- `Int.sumRange_congr`, `Int.sumRange_add`, `Int.sumRange_neg`.
- `Int.sumRange_sub` — **subtraction inside a finite sum**, the deciding lemma.
- `Int.sumRange_ofNat` — the ℕ→ℤ bridge a lattice-point count needs.
- `Int.modEq_sumRange` — the mod-2 reader, **unconditional in the modulus**.
- `Int.neg_add` — a ring lemma the prelude had proved inline and never stated.

Nine ledger rows; `validate-facts.py` 2511 facts / 0 errors;
`check-settled-fact-statements.py` PASS.

## What a consumer still needs

Not built, because none was needed to unblock the aggregate:
`sumRange_split`, `sumRange_shiftFront`, `sumRange_const`, `sumRange_swap`
(Fubini over ℤ), and a scaling lemma `Σ(c·f k) = c·Σf`. All five have
`prodRange` analogues that transport by the same route.

For Eisenstein's lemma itself, the three residues ADR-1260 named are unchanged:
the floor-counting family (the largest — it fights `Nat.div`/`Nat.mod` being
stuck at symbolic arguments), Euclid's lemma for the side condition, and step
1's mod-2 bookkeeping, which is what this lane's three headline lemmas were
built for.
