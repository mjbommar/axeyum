# Lane `fo-diagonal-lemma` — Q with order (W3-7, fourth slice)

<!-- plan-section: lane-status -->

**`FO.Qle` — Robinson's Q extended by six order axioms, its ℕ model and its
consistency; nine declarations, all axiom-free** (`PARTIAL`, fo-diagonal-lemma,
2026-09-06, ADR-1669).

Status: **deliverable 1 landed**; deliverables 2–4 not attempted (scope narrowed
mid-session by the coordinator after a process restart).

## What landed

`crates/axeyum-lean-kernel/src/fo_order.rs` — `FO.Qle`, Robinson's Q extended by
six order axioms over the `<` that `fo_robinson.rs` already had in the signature
but left unconstrained. Nine declarations, all axiom-free:

| name | kind | type |
| --- | --- | --- |
| `FO.Qle` | definition | `FO.Context` |
| `FO.Qle.axLtZero` | definition | `FO.Formula` |
| `FO.Qle.axLtSuccCases` | definition | `FO.Formula` |
| `FO.Qle.axLtSuccStep` | definition | `FO.Formula` |
| `FO.Qle.axLtSelfSucc` | definition | `FO.Formula` |
| `FO.Qle.axLtAddRight` | definition | `FO.Formula` |
| `FO.Qle.axLtDest` | definition | `FO.Formula` |
| `FO.Qle.natModels` | theorem | `Π v, FO.ctxSat AxNat FO.natStructureQ FO.Qle v` |
| `FO.Qle.consistency` | theorem | `Not (FO.Provable FO.Qle FO.Formula.bot)` |

Also `crates/axeyum-lean-kernel/examples/fo_order_inventory.rs` — the
fail-on-absence checker for the two new facts, baselined against
`build_fo_robinson_prelude` so its default report is exactly this slice's nine
rows.

Facts: `F:fo-qle-order-context`, `F:fo-qle-consistency`.
Decision: ADR-1669.

## The two decisions worth carrying forward

- **`≤` cannot be a second symbol.** `FO.natStructureQ`'s relation family is
  `rel2 k x y := Nat.lt (Nat.add x k) y` — the index adds on the LEFT, and
  `Nat.le x y` is an increment on the RIGHT, so no index of that family is
  `Nat.le`. `x ≤ y` is spelled `x < S y` throughout.
- **The binary axioms bind `y` OUTER and `x` inner, and that is forced.**
  `all_elim` puts the outer instance under `FO.Term.subst t FO.Subst.shift`,
  which is unrepairable for a `Π (t : FO.Term)`-bound term. Numeral outer,
  arbitrary term inner is the only order the next slice can instantiate.

## What did NOT land, with sizing

- **Negative numeral twin** `a ≠ b → Qle ⊢ ¬(ā = b̄)`. ADR-1651 sized this as
  "generalise five helpers over the context"; ADR-1669 withdraws that as
  pessimistic — `FO.Provable.weaken` lifts a `Qle` derivation into `cons φ Qle`
  in one step, so only the rules that already take a context argument need one.
  Remaining: three object derivations plus a double `Nat.rec`. ~400–500 lines,
  no new kernel machinery.
- **Bounded case split** `Qle ⊢ ∀z (z < S n̄ → z = 0̄ ∨ … ∨ z = n̄)`. Needs a new
  `FO.Qle.upto` definition plus a `Nat.rec`. **Unmeasured risk flagged**: the
  object-level `∀` form needs `all_intro` over a non-empty context, and no
  derivation in this group has ever used `all_intro` at anything but `nil`.
  Whether `FO.Context.shift FO.Qle` reduces back to `FO.Qle`, and at what cost,
  must be measured with a throwaway derivation before a lane commits to it.
- **Uniqueness of representation** for `pair`. Route written out in ADR-1669.
  The real obstruction is that the bound `m = 2·pair(a,b)` is symbolic, so the
  disjunction has symbolically many disjuncts and eliminating it needs a
  uniform-family eliminator none of the four slices has needed.
- **Diagonal lemma.** Blocked on the above. Gödel I stays open and
  hypothesis-carrying.

## Landed changes

| date | change | commits |
| --- | --- | --- |
| 2026-09-06 | `FO.Qle` scaffold: six order axioms, context, ℕ model, consistency | `7d47c7c91` |
| 2026-09-06 | inventory checker, two facts, ADR-1669, lane status | (this commit) |
