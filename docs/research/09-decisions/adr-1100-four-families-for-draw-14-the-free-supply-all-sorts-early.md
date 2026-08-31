# ADR-1100: Four families for draw 14 — the free supply all sorts EARLY, so the fourth has to be built late

Status: accepted
Date: 2026-08-31
Index-summary: ADR-1095 measured that a draw needs >= 4 fresh families
(`assign_partitions` assigns `held-out` only at cycle index `0, 3, 6, …`, so
`n` fresh families give `ceil(n/3)` held-out ones and R5 needs 2) and, having
found at most 3 constructible, declined. This lane re-measured on a freshly
rebuilt environment and found ADR-1095's supply search was answering a
slightly wrong question: the constraint is not "four families" but "cycle
indices **0 and 3** must both be held-out-viable", and **every** family
constructible without new work sorts early by its first Mathlib module name
(`Batteries.Data.Nat.Bisect`, `Init.Data.Nat.MinMax`,
`Mathlib.Data.Int.Fib.Basic`), so the free supply can fill index 0 and can
never fill index 3. Declared four definitions, construction-only per ADR-0653
— `Nat.Abundant`/`Nat.Deficient` (opening
`Mathlib.NumberTheory.FactorisationProperties`, 15 screened rows, the
late-sorting held-out-viable family the gap needed) and
`Nat.stirlingFirst`/`Nat.stirlingSecond` (opening
`Mathlib.Combinatorics.Enumerative.Stirling`, 16 rows, a topically fresh
`train`-slot option). Two independent 4-family layouts now clear R5, R9, R11's
topic and vocabulary signals and R12 against the real `select()`/`guard()`;
the only remaining refusal in both is R11's authorable **disclosure** step,
which a draw lane satisfies by recording the environment sweep in
`holdout-adjacency-review-v1.json`. Held-out isolation `held_out=146` before
and after.

Related: ADR-1095 (draw 13 declined; derived the `ceil(n/3)` mechanism this
ADR builds against, and searched the supply side without separating the sort
position), ADR-1060 (declared `Nat.avg`/`Nat.pair` and the min/max family —
the two free families this draw stands on), ADR-1045 (draw 12 declined),
ADR-0653 (an unblocking lane declares the construction and nothing else),
ADR-0695/ADR-0950 (R12, the closed-evaluation screen), ADR-0768 (R11, the
adjacency screen and its disclosure review), ADR-0542 (the amendment ledger)

## Context

Three consecutive draws declined with the mathematics queue below its floor
(4 dispatchable mirrors against 10, guard `G7 queue-below-floor`). ADR-1095
isolated the mechanism and it is not contamination: `_with_cycle` sorts the
FRESH family set by `FAMILY_MODULES[f][0]` and walks
`PARTITION_CYCLE = (held-out, development, train)`, restarting per draw. So
held-out lands at indices `0, 3, 6, …`, `n` fresh families give `ceil(n/3)`
held-out ones, and R5's minimum of two is unreachable below `n = 4`.

ADR-1095 then searched for a fourth family, exhaustively over
`propose-nursery-refill.py`'s `>= 10 hygiene survivors` list, and found at
most one more was constructible. It declined.

## What that search missed, measured

ADR-1095's conclusion — "at most 3 families" — is right about the modules it
looked at and wrong as a statement of the blocker, and the difference matters
because it points at completely different work.

Re-measured here against a freshly rebuilt `shape_search --release` (2589
declarations at session start, eleven more than ADR-1095's own 2583) by
running the real `select()` over EVERY un-owned module in the pinned
inventory, not only the ones the hygiene screen surfaces:

| family | modules | real pool | held-out viable? |
| --- | --- | --- | --- |
| `natural-avg-pair` | `Batteries.Data.Nat.Bisect` + `Mathlib.Data.Nat.Pairing` | 15 | **yes** |
| `natural-minmax` | `Init.Data.Nat.MinMax` | 28 | **yes** |
| `natural-fib-and-bitwise` | `Mathlib.Data.{Int,Nat}.Fib.Basic` + `Mathlib.Data.Nat.Bitwise` | 20 | no |
| `natural-factorization` | `Factorization.Basic` + `Factors` + `Multiplicity` + `PrimeCounting` | 11 | no |

So a fourth family DID exist with no new work at all — a combination over
four number-theory modules, 11 real candidates, which ADR-1095's
`>= 10 hygiene survivors` list does not surface because no single member
clears the floor. Registering it gives `n = 4` and satisfies R5.

It still does not give a draw, and this is the finding:

    natural-avg-pair                 index 0  held-out
    natural-minmax                   index 1  development
    natural-fib-and-bitwise          index 2  train
    natural-factorization            index 3  held-out
    GUARD REFUSED: R11 … natural-factorization: vocabulary: 9 of 10 rows are
      about constants a development/train family publishes (allowance 5) --
      Nat.Prime (natural-prime-arithmetic), Odd (integer-parity),
      Nat.choose (natural-binomial), Nat.Coprime (natural-coprimality)

**The real constraint is positional.** Cycle indices 0 and 3 are the held-out
slots, so a draw needs two families that are *individually* held-out-viable
AND that land in those two positions under the lexicographic sort. Screening
every candidate against R9, R12 and R11's two hard signals gives:

- **Index 0 is comfortable.** `Batteries.Data.Nat.Bisect` sorts before
  everything else in the candidate space, and `natural-avg-pair` is clean
  (reproducing ADR-1060's and ADR-1095's own numbers a third time, on a
  third environment).
- **Index 3 is the whole problem.** Everything that sorts late enough is
  number theory over vocabulary a development/train family already
  publishes, or is R9/R12-contaminated. The four un-owned late candidates
  reaching the floor with no new work all fail: `natural-factorization` on
  vocabulary (9 of 10), `natural-fib-and-bitwise` on topic + vocabulary +
  R9 + four R12 rows, and the `Choose.*` and `Prime.*` modules on topic.

That is why ADR-1095's three-family result and this ADR's four-family result
do not contradict each other. Adding a *fourth* family is easy; adding a
family that can be *held out at index 3* is what needed a construction.

## Decision

**Declare four definitions, construction-only (ADR-0653), and no theorem
about any of them.**

### `Nat.Abundant` / `Nat.Deficient` — the index-3 family

`crates/axeyum-lean-kernel/src/nat_prelude/abundant_deficient.rs`. Opens
`Mathlib.NumberTheory.FactorisationProperties`: **15 screened rows**, R9
0/10, R12 0/10, topic segment `FactorisationProperties` published by no
development/train family, and its first module sorts after every other
candidate — the one late, topically fresh slot in the whole space.

    Nat.Abundant  n := Lt (mul 2 n) (sumDivisors n)
    Nat.Deficient n := Lt (sumDivisors n) (mul 2 n)

Mathlib states both against `∑ i ∈ n.properDivisors, i`. This kernel has no
`Finset`, so there is no proper-divisor sum; what it has is
`Nat.sumDivisors` (`perfect.rs`), the sum of every divisor in `[0,n]`, and
`Nat.Perfect n := sumDivisors n = 2 * n` already states perfection in exactly
that subtraction-free form for exactly that reason. For `n >= 1`,
`sumDivisors n = (∑ properDivisors n) + n`, so `2n < sumDivisors n` is
Mathlib's proposition; at `n = 0` both sides are `0` and both predicates are
`Lt 0 0`, matching Mathlib's own `Nat.not_abundant_zero`.

Per the mirror-flip criterion this is the `Nat.minFac`/`Nat.nth` case: our
definitional body is provably equivalent to, not definitionally identical
with, Mathlib's, so every `ml430` mirror against Mathlib's predicates stays
`open`.

### `Nat.stirlingFirst` / `Nat.stirlingSecond` — an index-2 option

`crates/axeyum-lean-kernel/src/nat_prelude/stirling.rs`. Opens
`Mathlib.Combinatorics.Enumerative.Stirling`: **16 screened rows**, R9 0/10,
R11 fully clean, and Mathlib's own recurrences verbatim over the same
two-argument recursor shape as `Nat.choose`.

**It is NOT held-out viable, and that is measured rather than assumed.**
`Nat.stirlingFirst_zero` is the closed evaluation `stirlingFirst 0 0 = 1`,
which R12 refuses for a held-out row the moment the definition lands, and it
sorts into the alphabetically-first ten a draw takes. So the family is a
`development`/`train` family, and its value is that it gives index 2 a
topically fresh option — a draw need not register the `Fib`/`Bitwise`
combination (topic segments a development family publishes) merely to fill
that slot.

## Verification

Every number below is from the real `select()`/`assign_partitions()`/`guard()`
imported from `scripts/gen-autogenesis-nursery-refill.py`, run against the
committed environment snapshot AFTER the declarations landed (2593
declarations, refreshed from a rebuilt `shape_search --release`). Nothing is
simulated; `FAMILY_MODULES` is patched in memory only, never written, since
authoring a draw is the next lane's job and not this one's.

**Control, reproducing ADR-1095's refusal** (three families, all free):

    natural-avg-pair  held-out | natural-minmax  development
    natural-fib-and-bitwise  train
    GUARD REFUSED: R5 the refill adds 1 held-out families

**Layout A** (four families, one new construction pair used):

    [0] natural-avg-pair                  held-out     rows=10
    [1] natural-minmax                    development  rows=10
    [2] natural-fib-and-bitwise           train        rows=10
    [3] natural-factorisation-properties  held-out     rows=10

**Layout B** (four families, both new construction pairs used):

    [0] natural-avg-pair                  held-out     rows=10
    [1] natural-minmax                    development  rows=10
    [2] natural-stirling-numbers          train        rows=10
    [3] natural-factorisation-properties  held-out     rows=10

Both reach **exactly one** remaining refusal, and it is the same one in each:

    R11 … natural-avg-pair: disclosure: the kernel environment declares
      1 stem(s) [('avg', 'Nat.avg', 1)] and no review is recorded …
        natural-factorisation-properties: disclosure: … 4 stem(s)
      [('prime','Int.Coprime',99), ('abundant','Nat.Abundant',1),
       ('deficient','Nat.Deficient',1), ('perfect','Nat.Perfect',1)] …

R5 is satisfied in both (two held-out families). R9 is 0/10 on both held-out
families. R12 is 0/10 on both. R11's `topic` and `vocabulary` signals are
clean on both — confirmed independently by calling `screen_family` with
`require_disclosure=False`, which returns zero reasons for each.

**The disclosure is deliberately left open.** It is a human review step by
design (ADR-0768: "the review must reproduce the LIVE sweep exactly; that is
what makes it a disclosure rather than a rubber stamp"), and writing one
asserting diligence this lane did not perform would be the
checker-that-cannot-fail defect wearing a paper trail. The draw lane records
the sweeps above verbatim in
`artifacts/autogenesis/holdout-adjacency-review-v1.json` after reading the
declarations they name against the ten drawn statements.

One thing that review must actually look at, flagged here rather than left to
be discovered: `Nat.Perfect` exists in this kernel and our `Nat.Abundant`
and `Nat.Deficient` are stated against the SAME `Nat.sumDivisors`. That makes
the family's four trichotomy rows (`abundant_iff_not_perfect_and_not_deficient`
and siblings) an arithmetic trichotomy on `sumDivisors n` against `2n` rather
than a factorisation argument. Nothing in our development proves any of them,
so the family is blind; but a reviewer should know the rows are easier than
the module name suggests.

**Held-out isolation is unchanged**:
`AUTOGENESIS_HOLDOUT_ISOLATION|held_out=146|files_scanned=1110|settled=0|references=0|verdict=PASS`
before and after. `artifacts/autogenesis/nursery-v1.json` was never touched,
no fact moved partition, and no `FAMILY_MODULES` edit is committed.

**Kernel gates**: `cargo test -p axeyum-lean-kernel --lib nat_prelude::` is
276 passed / 0 failed (up from 273, the three new evaluation-test functions);
`cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` is clean.
`every_nat_declaration_is_checked_and_axiom_free` reads the ENVIRONMENT and
failed naming all four new definitions the moment they landed, which is what
that assertion is for; they are registered in `definition_names` and it
passes.

## Consequences

- **Draw 14 has two independent 4-family layouts** and both are one
  authorable review row away from `GUARD PASSED`. The draw lane authors
  `FAMILY_MODULES`/`FAMILY_ROUTES`, the two disclosure reviews, and
  regenerates `nursery-v2-extension.json`. This lane enables a draw; it does
  not author one.

- **More families is NOT automatically better, and a draw lane will get this
  wrong.** The held-out slots are indices 0 and 3, so ADDING a family can
  push a contaminated one into a held-out slot. Concretely: the five-family
  set `{avg-pair, minmax, stirling, fib-and-bitwise, factorisation-properties}`
  puts `Mathlib.Data.Int.Fib.Basic` at index 3, and R11 refuses it on topic
  and vocabulary and R9 and R12. Pick the four; do not add the fifth.

- **The next unblock lane should ask a positional question, not a counting
  one.** "Which family can sit at cycle index 3?" is the constraint;
  "how do we reach four families?" is not, and answering the second is how
  three consecutive draws were sized. The measured index-3 candidates still
  needing constructions, all topic-clean and all R9/R12-clean once their
  constants exist, are (pool size, constructions needed):
  `Mathlib.Data.Nat.Factorization.Root` (18, `Nat.floorRoot` +
  `Nat.ceilRoot`), `Mathlib.Data.Nat.Find` (15, `Nat.find` +
  `DecidablePred`), `Mathlib.Data.Nat.MaxPowDiv` (10, `Nat.divMaxPow` +
  `padicValNat`).

- **`Mathlib.Data.Nat.Count` measures held-out-viable and is NOT, and the
  screen cannot see why.** It reports 22 screened rows, R9 0/10, R12 0/10,
  R11 clean once `Nat.count` and `DecidablePred` exist. But `Nat.countRange`
  is already in this kernel with `countRange_zero`, `countRange_succ`,
  `countRange_le`, `countRange_const_true` and more from the totient work,
  and `Nat.count p n` is that function — so `Nat.count_zero`,
  `count_succ`, `count_le`, `count_true` and `count_monotone` are already
  proved here under other names. That is R11's documented shape-2 blindness
  (a differently-named theorem), and it is exactly what the disclosure
  review exists to catch. **Do not open that family for held-out.** Named
  here so the next lane does not spend two definitions discovering it.

- **`propose-nursery-refill.py`'s ready list is not the candidate space.**
  ADR-1095 used it as an exhaustive search, correctly noting it overcounts;
  what was not noticed is that it also UNDERCOUNTS the space of *families*,
  because it screens per module and a family may combine several below-floor
  ones. The real search is over module SUBSETS with the real `select()`, and
  it found `natural-factorization` (11 rows, 4 modules, none of which clears
  the floor alone) which that list cannot surface.
