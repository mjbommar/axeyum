# Lane 373 — the unrestricted least-number principle implies excluded middle

<!-- plan-section: lane-status -->

## Status

**DONE.** ADR-0603 row 2 for the least-number principle over the naturals is
landed, kernel-checked, axiom-free, and registered in the fact ledger with its
converse. This is the first row-2 result in the repository that is not about the
reals, and it is strictly stronger than the two that are.

## What landed

`crates/axeyum-lean-kernel/src/nat_prelude/least_number.rs` — five theorems, all
admitted by `Kernel::add_declaration` on the first attempt, all with an empty
`axiom_footprint`. Rendered types read from
`nat_theorem_inventory` (`--release`), one name per invocation:

```text
Nat.lnp_unrestricted_implies_em :
  (∀ (Q : AxNat → Prop),
     (∃ n, Q n) → ∃ m, And (Q m) (∀ k, AxNat.lt k m → Not (Q k)))
  → ∀ (P : Prop), Or P (Not P)

Nat.em_implies_lnp :
  (∀ (P : Prop), Or P (Not P))
  → ∀ (Q : AxNat → Prop),
      (∃ n, Q n) → ∃ m, And (Q m) (∀ k, AxNat.lt k m → Not (Q k))

Nat.lnp_of_pointwise_decision :
  ∀ (Q : AxNat → Prop), (∀ n, Or (Q n) (Not (Q n)))
  → (∃ n, Q n) → ∃ m, And (Q m) (∀ k, AxNat.lt k m → Not (Q k))

Nat.lnp_bounded_search :
  ∀ (Q : AxNat → Prop), (∀ n, Or (Q n) (Not (Q n))) → ∀ n,
    Or (∀ k, AxNat.lt k n → Not (Q k))
       (∃ m, And (AxNat.lt m n) (And (Q m) (∀ k, AxNat.lt k m → Not (Q k))))

Nat.lnp_decidable :
  ∀ (dec : AxNat → Bool) (n : AxNat), Eq Bool (dec n) Bool.true
  → ∃ m, And (Eq Bool (dec m) Bool.true)
             (∀ k, AxNat.lt k m → Eq Bool (dec k) Bool.false)
```

Facts: `F:nat-lnp-unrestricted-implies-em` (row 2) and `F:nat-lnp-decidable`
(the decidable-fragment exact form). ADR-0725 records the two design decisions
ADR-0716 did not make.

## The three things a reviewer should check first

1. **The price is EXACTLY excluded middle, not at least excluded middle.**
   `Nat.em_implies_lnp` is the converse, one line from
   `lnp_of_pointwise_decision` at `fun n => em (Q n)`.
   `nat_prelude_tests::the_unrestricted_lnp_and_excluded_middle_are_pinned_as_an_exact_equivalence`
   builds `L` and `E` once and requires the two declared types to be literally
   `L → E` and `E → L` for the same two `ExprId`s — structural equality, not
   `def_eq`, not prose.
2. **Non-vacuity.** `Nat.lnp_of_pointwise_decision` is the *identical statement
   one hypothesis stronger*, so a reader can see the boundary is the
   decidability hypothesis and not a missing proof. `Nat.lnp_decidable`
   instantiates it at a `Bool`-valued predicate. `Nat.least_divisor_search`
   (`min_fac.rs`) is the older, independent witness — `lnp_bounded_search`'s
   shape specialised to divisibility, which `minFac`'s minimality already runs
   on. The same test also scans the whole environment and requires that NO
   declaration has type `L` or type `E`, with the positive control being the
   identical scan finding `lnp_unrestricted_implies_em` by its own type.
3. **Stronger than the analysis row 2s.** `creal/ivt_boundary.rs` and
   `creal/extreme_value.rs` each reduce to deciding the sign of one arbitrary
   real — analytic LLPO, consistent with BISH, and *not* excluded middle for an
   arbitrary proposition. This row gives `P ∨ ¬P` for every `P : Prop` the
   kernel can form.

## Two things that went wrong, recorded because they generalize

**One of my negative controls was VACUOUS and mutation testing is what found
it.** The first draft applied `Nat.lnp_of_pointwise_decision` to a `Prop` where
a `Nat → Prop` was expected, asserted `is_err()`, and passed — on a *sort
mismatch*, having nothing to do with the distinction it claimed to test.
Substituting the real hypothesis for the "bogus" one left it green, which is the
tell. The control now plugs the decidable form into the unrestricted hypothesis
slot; both negative controls in this lane are mutation-verified to kill exactly
one test.

**I hand-derived `depends_on` and got it wrong.** My search matched only
`formal.kernel_theorem`, so it missed three registered facts that the ledger
records under other shapes. `scripts/check-fact-depends-derived.py` derives the
edges from the proof term itself and refused the ledger until they were added
(`F:logic-bool-false-ne-true`, `F:nat-le-succ-succ`, `F:nat-zero-le`). Do not
hand-list `depends_on`; run `--fix` and let the proof term answer.

## Checks run (all foreground)

| check | result |
| --- | --- |
| `cargo test -p axeyum-lean-kernel --lib nat_prelude::` | **214 passed, 0 failed** (was 208) |
| `every_nat_declaration_is_checked_and_axiom_free` | passes; covers all five new names |
| `cargo fmt --all --check` | clean |
| `cargo clippy -p axeyum-lean-kernel --all-targets --all-features -- -D warnings` | clean |
| `python3 scripts/validate-facts.py` | 2267 facts, **0 errors** |
| `python3 scripts/check-autogenesis-holdout-isolation.py` | `held_out=116\|settled=0\|references=0\|verdict=PASS` |
| `python3 scripts/gen-adr-index.py` | `rows=631`, exit 0 |

Every `checker_command` in both facts was run in **both** directions: the real
name prints `1` and exits 0, a fabricated name prints `0` and exits 1
(confirmed with an explicit `PIPELINE_STATUS`, not `echo $?` after a pipeline).

NOT run, deliberately, per the lane brief: `cargo test --workspace` and
`./scripts/check.sh`.

## What is left

- **The two phrasings of minimality are not bridged.** ADR-0716 writes the
  minimality clause `∀ k, P k → m ≤ k`; the landed form is
  `∀ k, Lt k m → Not (P k)`. They are interderivable over this prelude through
  `Nat.lt_or_ge` (landed, axiom-free), but **that bridge is not a declaration**,
  so the equivalence of the phrasings is an argument in ADR-0725 and not a
  checked theorem. Cheap to close; someone quoting ADR-0716's phrasing against
  the landed one should close it first.
- **Row 2′ (ADR-0716 §3) is untouched.** Unique factorization's multiset
  uniqueness is an *expressiveness* gap, not a decision gap, and nothing here
  bears on it.
- The same row-2 shape should transport to ℤ and ℚ almost verbatim — the
  predicate uses only `0`, `1`, `Eq` and the order — but the interesting
  question is whether a *different* boundary shows up there, not whether this
  one repeats.
