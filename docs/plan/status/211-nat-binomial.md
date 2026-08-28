# Lane: nat-binomial — close the `Nat.choose` binomial backlog

<!-- plan-section: lane-status -->

**Your lane's block (`DONE for this dispatch`, nat-binomial, 2026-08-28).**
Landed the one closeable fact in the `natural-binomial` open set;
the other six open facts in the family are genuinely blocked, not missed.

Of the seven open `natural-binomial` facts (verified all 20 family entries
are `development`, none `held-out`, per `nursery-v1.json`):

- **Closed:** `F:ml430-nat-choose-mono-a1af9c18` (`Nat.choose_mono`,
  `Monotone (fun a => a.choose b)`). Its Monotone unfolding is exactly
  `Nat.choose_le_choose` with arguments `(a, a', c)` permuted so the fixed
  column `c` is outermost — no new induction, just a permuted application.
  `crates/axeyum-lean-kernel/src/nat_prelude/choose.rs::declare_choose_mono`.
  kernel-lean, axiom-free (verified via `theorem_axiom_footprint`).
- **Not actionable, skipped, both definitions confirmed absent from a
  FRESH build (2,006 declarations indexed, `shape_search --include-constructed`,
  exit 1 = ABSENT on both):**
  - `F:ml430-nat-factorial-dvd-ascfactorial-44a4e641` — needs `Nat.ascFactorial`
  - `F:ml430-nat-factorial-dvd-descfactorial-bbf6124f` — needs `Nat.descFactorial`
  - `F:ml430-nat-multichoose-one-b210386a` — needs `Nat.multichoose`
  - `F:ml430-nat-multichoose-one-right-7755072d` — needs `Nat.multichoose`
  - `F:ml430-nat-multichoose-zero-right-6ef827c8` — needs `Nat.multichoose`

  Defining `ascFactorial`/`descFactorial`/`multichoose` is a separate task
  (a new `Nat` definition + equation lemmas), out of scope for this dispatch.
- **Not touched, by design:** `F:ml430-mutation-edb05acf07d9ef3f9f8232fc` is
  an outcome-blind mutation fixture (`n.choose n = 0`, deliberately false —
  the real `choose_self` proves `= 1`). It is `open` by construction and has
  no expected truth value; it is not a theorem to close.

`nat_prelude` count: **74 defs + 373 theorems = 447 -> 74 defs + 374 theorems
= 448** (recounted from `theorem_names`/`definition_names`, not hand-incremented).
`the_build_is_deterministic` and `every_nat_declaration_is_checked_and_axiom_free`
both green; full `nat_prelude` sweep 108 passed / 0 failed.

**Next lane:** the five blocked facts need `Nat.ascFactorial`, `Nat.descFactorial`,
and `Nat.multichoose` defined (with their equation lemmas) before they are
reachable at all — that is real new-definition work, not a re-derivation of
something already in the tree.

<!-- plan-section: landed-changes -->

| 2026-08-28 | nat-binomial | `Nat.choose_mono` via permuted `choose_le_choose`; closes `F:ml430-nat-choose-mono-a1af9c18`, kernel-lean, axiom-free; nat_prelude 447->448 |
