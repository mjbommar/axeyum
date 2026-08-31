# Lane: unblock-draw-16 — make draw 16 possible

<!-- plan-section: lane-status -->

Status: COMPLETE (2026-08-31). The measurement is decisive and the brief's
premise was inverted; three of the five constants a verified layout needs are
landed. **Draw 16 is not yet authorable** — see "What remains".

## What this lane was asked to do

Find or build what lets a fifth family sit at cycle **index 3**, and re-screen
with the real machinery. Do not author the draw.

## The headline finding: index 3 is reachable, index 0 is not

ADR-1100's positional framing — "the free supply all sorts EARLY, so it fills
index 0; index 3 needs a late-sorting family" — was true when written and is
**false today**, because draw 15 consumed exactly that free early supply
(`natural-avg-pair`, `natural-minmax`, `natural-stirling-numbers`).

Measured exhaustively over all 265 un-owned modules and every 1-, 2-, 3- and
4-element construction subset, against the real `select()` /
`assign_partitions()` / `screen_family()` / `is_closed_evaluation`:

- **One free family remains** — `Mathlib.NumberTheory.FactorisationProperties`,
  15 rows. It is the only free family R11 calls clean (vocab 4/10), and R12
  refuses it on two rows already decided by reduction (`Nat.Abundant 12`,
  `Nat.Deficient 1`; all three predicates verified present in the environment).
- Every other free family is R11-refused as held-out on topic or vocabulary.
- So **both** held-out slots (indices 0 and 3) now need a construction, and
  index 0 is the harder one.

Verified layout, run through the real machinery:

    [0] natural-primitive-recursion   Mathlib.Computability.Primrec.Basic   held-out
    [1] natural-fibonacci             Mathlib.Data.Int.Fib.Basic            development
    [2] natural-prime-divisibility    Mathlib.Data.Int.NatPrime             train
    [3] natural-integer-root          Mathlib.Data.Nat.Factorization.Root    held-out

    both held-out slots: R9 PASS, R12 PASS, R11 clean (vocab 0/10)

## Two screens nobody had run, and both changed a decision

No prior draw or unblock ADR asks what DECLARING a construction does to
families that are already frozen.

- **Frozen-family drawn-ten churn.** Declaring `Nat.count` swaps **five of
  `natural-nth-selector`'s ten** drawn rows — a held-out family from draw 7.
  A second, independent reason to keep `Mathlib.Data.Nat.Count` refused, on
  top of ADR-1100's shape-2 finding. Every other candidate set churns nothing.
- **Stale recorded review.** `check-holdout-adjacency.py` screens every
  held-out family including frozen ones, and refuses one whose recorded review
  no longer matches the live sweep. Declaring `Nat.ceilRoot`/`Nat.floorRoot`
  moves draw 11's `natural-nth-root` sweep from 11 `root` hits to 13 and
  **reds that gate**. The adjacency is real (`floorRoot` and `nthRoot` are both
  greatest-witness searches), so the re-review is the right work — but it is an
  unbudgeted cost of the index-3 route that no ADR named.

Both screens are cheap Python against existing machinery and should be run by
every unblocking lane before it writes code.

## What was landed

`Nat.unpairLeft`, `Nat.unpairRight`, `Nat.unpaired` — construction only
(ADR-0653), zero theorems, no fact registered.

`avg_pair.rs` records `Nat.unpair` as unreachable because Mathlib's returns
`Prod`. That is right about the CONSTANT and wrong about the unpairing: the two
projections have type `Nat -> Nat` and `Nat.unpaired` has Mathlib's own
`(Nat -> Nat -> Nat) -> Nat -> Nat`, neither mentioning a product. The stale
note is corrected in place.

Effect: `Mathlib.Computability.Primrec.Basic` drops from three missing
constants to **two** (`Nat.Primrec`, `Nat.casesOn`).

## Verification

- `--lib unpair` 3 passed / 0 failed; `--lib nat_prelude::` **299 passed /
  0 failed** (was 296), the whole sweep.
- Mutation-verified in this lane's own worktree: transposing `unpairLeft`'s
  branch kills all three tests; dropping the `- s` correction kills all three
  and names the specific assertions. Restored and green.
- Environment 2629 -> 2685 (other lanes' work) -> **2688** (exactly +3, all
  three names present), from a `shape_search --release` rebuilt here.
- `gen-autogenesis-nursery-refill.py --check` OK at `env=2688`, manifest
  byte-identical across both snapshot refreshes.
- `check-autogenesis-holdout-isolation.py` `held_out=166 settled=0 PASS`
  before and after; nothing moved partition.
- `check-holdout-closed-evaluation.py` PASS;
  `create-autogenesis-nursery-dispatch-baseline.py --check` OK;
  `check-holdout-adjacency.py` 16 families / 0 refused;
  `check-shape-duplicates.py` OK.

## A gate that is red on `main`

`check-autogenesis-nursery.py` exits **1**, with `2 cross-population
partition-leak violation type(s)` over `depends_on` components spanning
development / train / longitudinal. Verified from a detached worktree at `main`
(69eb494e9): identical message, unrelated to this lane, nothing held-out
involved.

This lane's first read of it printed a green `exit=0`, because the check used
`| tail -3; echo "exit=$?"` — the banned pipeline-`$?` idiom, hit on the very
command meant to establish a baseline.

## What remains, for the next lane

1. **Declare `Nat.Primrec` and `Nat.casesOn`** to open
   `Mathlib.Computability.Primrec.Basic` (11 rows, zero boundary equations in
   the drawn ten, zero ground evaluations, R11 clean, and measured to churn
   nothing and stale no review). Caveat: an inductive `Prop` admits no
   evaluation test, so it needs discriminating checks designed for an inductive
   rather than a numeral table.
2. **Declare `Nat.ceilRoot`/`Nat.floorRoot`** for index 3, and redo draw 11's
   `natural-nth-root` review in the same lane. The 3-of-10 boundary reading is
   relative to MATHLIB's definition; ours cannot be (no `Finsupp`), so the
   count must be re-measured against whatever construction is built.
3. Then a draw lane authors `FAMILY_MODULES`/`FAMILY_ROUTES` and the two R11
   disclosure reviews.

Full argument, tables and numbers:
[ADR-1220](../../research/09-decisions/adr-1220-index-0-is-now-the-binding-slot.md).

## Landed changes

| commit | what |
| --- | --- |
| `chore(autogenesis)` | environment snapshot 2629 -> 2685, manifest churn checked |
| `feat(nat)` | `Nat.unpairLeft`/`unpairRight`/`unpaired`, construction only |
| `chore(autogenesis)` | snapshot 2685 -> 2688 for the three definitions |
| `docs(adr)` | ADR-1220 and the `avg_pair.rs` correction |
