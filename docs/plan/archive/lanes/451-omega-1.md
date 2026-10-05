# Lane: omega-1 — a linear-arithmetic decision procedure that EMITS kernel terms

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, omega-1, 2026-09-03).** `crate::linarith` is the
first *tactic-layer* producer: quantifier-free linear arithmetic over ℕ and ℤ
that returns a **kernel proof term**, not a verdict. Untrusted search (a bounded
Farkas certificate), trusted checking (`Kernel::add_declaration`). ADR-1576
records the decision, the cost datum and the two measured fragment edges.

**The number.** Fifteen hand-written proofs retired — ten in `nat_prelude`, five
in `int_prelude`, **184 source lines deleted**, 45 added (five of those 45 are the
`use` lines that bring the producer into scope). Each theorem is
re-admitted at a type that `kernel_declaration_projection` shows *byte-identical*
over all 15,887 rows (prelude / kind / name / axiom-footprint-size /
type-constants / rendered type), and all fifteen still measure axiom footprint 0.
Exactly fifteen theorems changed, and only in their proof-dependency columns.

    nat_prelude  le_refl_thm  le_succ  succ_le_succ  le_of_lt_succ  lt_succ_self
                 lt_succ_of_le  lt_add_one  le_succ_of_le  zero_lt_succ
                 le_of_lt_add_one
    int_prelude  add_left_comm  add_neg_cancel_left  add_neg_cancel_right
                 add_le_add_three  add_le_of_le_sub_left

**Cost**, `--release`, 200 emissions per shape, prelude built once per shape
(`cargo run --release -p axeyum-lean-kernel --example linarith_cost`): **0.455 –
14.659 ms per term end to end**, kernel recheck included. The recheck is the
*minority* of that (10–45%); the emitter's own normalizer is the expensive half,
and ℤ costs 3–7x ℕ because `Int.add` case-splits on both arguments so nothing
ι-reduces. Single unpinned run on a shared box — order of magnitude, not a
baseline to ratchet against.

**The guard that decides whether any of it is worth anything.** Three corrupted
certificates — a multiplier off by one, a residual off by one, and a hypothesis
slot carrying a proof of a *different true* proposition — and in each case the
procedure EMITS a term and the **kernel** refuses it, run with the procedure's
own arithmetic check deliberately disabled. A corruption caught only by our own
bookkeeping proves nothing about the trust anchor. A positive control sits
beside them (the uncorrupted certificate is admitted), and a fourth test keeps
the procedure's own check honest by requiring it to decline the same corruption
with `verify = true`. Both batteries exist over ℕ and over ℤ. 52 tests total.

**Sized negatives, each pinned by a test rather than asserted in prose.**

- Over ℤ a `<` HYPOTHESIS contributes only `a ≤ b` (`le_of_lt`); its strictness
  is dropped, so `a < b ⊢ a + 1 ≤ b` **declines**. Recovering it needs
  `lt a b → le (a+1) b`, which `int_prelude` does not have — `lt_dest` gives
  `∃ i, b = a + ofNat (i+1)` and turning that into the `+1` form is a new lemma,
  not a rearrangement. Not built: a new `IntPrelude` field is a shared
  allocation point across lanes, for a capability nothing in the ledger needs.
- Over ℤ `Int.mul` is not in the fragment at all, not even by a literal, where
  the ℕ side handles a numeral multiplier. `Nat.mul x k` ι-reduces to a fold at
  a literal `k`; `Int.mul x k` is stuck at symbolic `x` whatever `k` is.
- The search is bounded (`MAX_MULTIPLIER = 4`, `MAX_HYPOTHESES = 8`) and
  declines above it rather than growing a coefficient. Every numeral here is
  unary, so a certificate with coefficient 40 is a term forming `succ⁴⁰ zero`.
  Fourier–Motzkin was considered and rejected for exactly this: recovering the
  emitter's multipliers from an FM refutation needs division by the negated
  goal's own multiplier, which is rational and reintroduces large numerals.

**The producer contract is born retired, and that is the finding.**
`artifacts/autogenesis/producer-contracts/linear-arithmetic-v1.json` validates
(`PRODUCER_CONTRACTS_OK|contracts=4|retired=2`) with a live population of
**zero**, under ADR-1510 rule 1. The shape is not what makes it zero: reading
all 245 open `Mathlib v4.30 source proposition` names — not running one
predicate — finds no quantifier-free linear-arithmetic proposition among them.
The two closest (`Int.add_one_le_of_not_le`, `Int.le_sub_one_of_not_le`) take a
NEGATED order fact as a hypothesis, which this fragment handles as a goal and
never as an assumption. Linear arithmetic is the part of this development that
was finished FIRST, by hand, so a procedure for it arrives to an empty dispatch
queue and a full retirement queue. **The contract system sizes dispatch and
cannot see fifteen retired proofs** — worth knowing before the next
tactic-layer producer hits the same wall.

**Two things the next lane should know, neither of them mine to fix.**

1. `scripts/tests/test_validate_producer_contracts.py` is RED on this tree and
   was red before this lane touched it — confirmed by moving
   `linear-arithmetic-v1.json` out and re-running (still one failure).
   `producer-contract-nat-coprime-family-v1`'s held-out overlap grew by
   `F:ml430-nat-exists-eq-pow-of-exponent-coprime-of-pow-eq-pow-17408247` and
   `KNOWN_HELD_OUT_SHAPE_MATCHES` was not updated. Deliberately not fixed here:
   that allowlist records blind evaluation population and belongs to whoever
   owns the nursery draw. `scripts/validate-producer-contracts.py` itself is
   green at exit 0.
2. **`Int.add_le_add_left`'s doc comment is wrong**, and it cost a debugging
   cycle. It reads `∀ (a b : Int), le a b → ∀ (c : Int), …`, but the
   declaration is `int_theorem(p.add_le_add_left, 3, …)` — all three integers
   bind BEFORE the hypothesis. Passing arguments in the documented order is a
   `TypeMismatch` naming two `ExprId`s and nothing else. Same for
   `add_le_add_right`. The declaration is the authority.

**Gates run.** `linarith::` 52 tests green (33 ℕ + 19 ℤ), `nat_prelude::` 408
green, `int_prelude::` 81 green, all `--release`; `cargo clippy -p
axeyum-lean-kernel --all-targets -- -D warnings` exit 0; `scripts/check-links.sh`
all links ok; `validate-producer-contracts.py` exit 0. **Did not run:** the
workspace-wide `cargo test --workspace` (timed out at 10 minutes on this box and
gates nothing this lane touched) and `just check` / `scripts/check.sh`.

<!-- plan-section: landed-changes -->

| 2026-09-03 | omega-1 | `crate::linarith`: a linear-arithmetic producer emitting kernel terms over ℕ |
| 2026-09-03 | omega-1 | ten `nat_prelude` order proofs retired to the producer, projection zero-diff |
| 2026-09-03 | omega-1 | the ℤ fragment, and five more retired proofs in `int_prelude` |
| 2026-09-03 | omega-1 | `linear-arithmetic-v1` producer contract, born retired against an empty live population |
| 2026-09-03 | omega-1 | ADR-1576 and the cost datum: 0.5–15 ms per emitted term, beside `ring_law_proof` |
