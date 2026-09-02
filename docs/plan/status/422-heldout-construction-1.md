# Lane: heldout-construction-1 — the ADR-1420 Route 1 construction that ends draw 19's four-module chokepoint

<!-- plan-section: lane-status -->

**Done (`DONE`, heldout-construction-1, 2026-09-02).** ADR-1556 refused draw 19
on a measurement — 3 viable held-out families over 40,668 distinct drawn tens,
the same four modules in every one, so R5's two module-disjoint held-out
families are unsatisfiable — and named ADR-1420 Route 1 as the unblock. This
lane is that route. Four Definitions landed (`Nat.isPrime`,
`Nat.primeCounting'`, `Nat.primeCounting`, `Nat.lcmUpto`), with evaluation tests
and **no theorem about any of them**; they open
`Mathlib.NumberTheory.PrimeCounting` (9 rows) and
`Mathlib.NumberTheory.Chebyshev` (3 rows), both topic-clean and disjoint from
the four blocking modules. `adr-1556-draw-19-screen.py` goes from exit **0** to
exit **1**, and `modules contributing a row to EVERY viable ten` goes from those
four modules to **`[]`**. Decision:
[ADR-1559](../../research/09-decisions/adr-1559-primecounting-and-lcmupto-are-the-construction-that-unblocks-draw-19.md).

No family was added to `FAMILY_MODULES`, no manifest row written, no partition
assigned, no held-out outcome named, no fact registered. The construction's
theorems do not exist, so there is nothing to register.

## Gates, before and after (each run bare, exit captured before any `grep`)

| gate | before | after | headline (after) |
| --- | ---: | ---: | --- |
| `adr-1556-draw-19-screen.py` | 0 | **1** | `env=3018 unowned_modules=25 unowned_rows=91 distinct_tens=64142 viable=196 disjoint_pairs=219 failures=2` |
| `gen-autogenesis-nursery-refill.py --check` | 0 | 0 | `entries=500 env=3018 development=180 held-out=190 train=130 screen_drift=31` |
| `check-holdout-adjacency.py` | 0 | 0 | 20 held-out families, **0 refused**, 4 undisclosed (advisory) — went red in between, see below |
| `check-holdout-adjacency.py --self-test` | — | 0 | 11 passed, 0 failed |
| `check-autogenesis-holdout-isolation.py` | 0 | 0 | `held_out=206 files_scanned=1114 references=0 PASS` |
| `check-holdout-closed-evaluation.py` | 0 | 0 | `held_out=206 closed_shaped=0 violations=0 snapshot_declarations=3018 PASS` |
| `check-partition-edges.py --baseline` | 0 | 0 | `drawn=716 crossing=198 baselined=198 violations=0 PASS` |
| `check-autogenesis-already-proved.py` | 0 | 0 | name-match report only, no new match |
| `validate-facts.py` | 0 | 0 | 2624 facts, 0 errors |
| `gen-py-prelude-fields.py` | 0 | 0 | `total=2923 nat=1059` (was 1055) |
| `gen-adr-index.py` | 0 | 0 | `rows=774` |
| `cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` | — | 0 | zero warnings, zero errors |
| `check-merge-hygiene.sh` | — | 0 | run last |

**What the screen's `failures=2` is.** One of the two IS the deliverable: the
assertion named `the refusal still holds` fails with `a disjoint pair EXISTS --
author draw 19`, which is the script's own documented success signal. The other
is a genuine finding about the screen rather than about the draw: its
minimal-cover pruning now **undercounts**, 37 viable against the exact pass's
196. ADR-1556 predicted the direction ("a superset does not draw the same ten,
because an added module's names can sort earlier") and asserted the two passes
agreed, which they did at 3 vs 3; with a richer pool they no longer do. The
EXACT pass is the authority and it is what `disjoint_pairs=219` comes from. The
control still fires (lifting ADR-1450's `Nat.Count` bar takes the search to 228
viable / 1,913 pairs), so the search is not broken — it is the pruning
shortcut that has expired, and the next lane to touch that script should
either drop the pruned pass or turn the equality assertion into a
`pruned <= exact` one.

## The gate this lane turned red, and the finding underneath it

`check-holdout-adjacency.py` reads the COMMITTED environment snapshot, and that
snapshot was **176 declarations behind the kernel** (2838 against a live 3014).
Refreshing it — which any lane that wants its own declarations to be visible to
the autogenesis screens must do — is what made the gate red. Isolated across
three snapshots, each run bare:

| snapshot | exit | refused |
| --- | ---: | --- |
| 2838 (the state on `main`) | 0 | none |
| 3014 (refreshed, WITHOUT this lane's declarations) | **1** | `natural-factorization-lcm`, `natural-max-power-dividing` |
| 3018 (refreshed, WITH them) | **1** | the same two |
| 3018, after the re-review below | **0** | none |

So the redness is not this lane's declarations — it is 176 declarations from
other lanes that the stale snapshot was hiding — but it sits squarely on this
lane's path, because the construction is worthless to the draw until the
snapshot sees it. **The finding: a disclosure review can only be as fresh as
the snapshot it is compared against, so a stale snapshot silently suspends R11's
environment signal.** Both refusals are `disclosure` refusals, which is the
mechanism working the moment it was given current data.

The repair was a real re-sweep, not a number bump, and it is recorded in the
two reviews' `finding` narratives:

* `natural-factorization-lcm`: `lcm` 20 → 21 and `factorization` 3 → 9. The six
  new `factorization` names (`Nat.factorization`, `Nat.factorizationAux`,
  `Nat.factorizationAuxPrime`, `Nat.factorization_prime`,
  `Nat.prodFactorizationAux`, `Nat.prod_factorization`) are the prime-factorization
  MULTISET construction and its product — a different function from the
  per-prime max split; the one new `lcm` name is this lane's `Nat.lcmUpto`, a
  fold over a RANGE that says nothing about a PAIR. Decisive check, run rather
  than argued: `--const Nat.factorizationLCMLeft --kind theorem --expect-absent`
  and the same for `…Right` are both ABSENT with a live positive control
  (`theorem=2440 ns Nat=1082`).
* `natural-max-power-dividing`: `prime` 111 → 122 (twelve added, one removed by
  a rename), `max` and `divmaxpow` do not move at all — 44 and 2. `divmaxpow`
  staying at 2 is the load-bearing number: those two are the definitions
  themselves. Not one of the twelve is a prime-INTERVAL statement, and
  `--const Nat.divMaxPow --kind theorem --expect-absent` is ABSENT.

Neither verdict changed; only the recorded sweep and the narrative. The
checker's own guard is shown non-vacuous by the sequence: it refused twice
before the re-review and refuses nothing after it.

## The construction, and the screen that chose it

Of 248 unowned modules, **196** are topic-clean, non-blocking and non-barred.
Only **five** of them reach `PER_FAMILY = 10` on their own with three or fewer
added constants, and **not one of those five is a mathematical construction** —
four need a typeclass instance or a `Char`/`List` layer and the fifth a binary
recursor. `Mathlib.Data.Nat.Choose.Central` is the largest single-construction
opening in the pool (`Nat.centralBinom` unlocks 14 rows, one line over the
`Nat.choose` this kernel already has) and is **refused on a path segment**:
`Choose` is published by `natural-binomial` and by
`natural-factorial-choose-and-squarefree`.

Run against the real `screen_family` / R9 / R12 over every bundle of at most
five non-blocking modules — a ten built only from modules disjoint from the four
blockers is module-disjoint from every ten viable today, so its existence is
exactly what R5 needs:

| declared | viable module-disjoint tens |
| --- | ---: |
| nothing (today) | 0 |
| `Nat.centralBinom` | 0 (topic-refused) |
| `Nat.lcmUpto`, `primorial` | 0 |
| `Nat.isPowerOfTwo`, `Nat.nextPowerOfTwo` | 0 |
| `Nat.FermatPsp`, `Nat.ProbablePrime` | 0 |
| `Nat.isPrime`, `Nat.primeCounting` (without the primed one) | 0 |
| `Nat.isPrime`, `Nat.primeCounting'` (without the unprimed one) | 0 |
| **the pair** | 5 |
| **the pair + `Nat.lcmUpto`** | **16, of which 8 carry no definitional row** |

`Nat.isPrime` is a divisor COUNT, not a trial division:
`beq (countRange (fun j => beq (n % (j+1)) 0) n) 2`. `countRange` already folds
over `j < n`, so the predicate needs no fuel recursion, no `Bool` conjunction
and no new recursion principle, and both degenerate rows fall out of the fold
rather than being chosen conventions. It is NOT Mathlib's `Nat.Prime` — a
`Bool` predicate with a different construction — so no `ml430` mirror against
`Nat.Prime` may be flipped on account of it; measured against the pinned
inventory, no Mathlib row is named `Nat.isPrime` and no row's type mentions it
(0 and 0), so it opens nothing by itself.

## The other finding: one candidate row is Mathlib's own defining equation

`Nat.primeCounting_eq_primeCounting'_succ : ∀ n, n.primeCounting = (n + 1).primeCounting'`
is `rfl` under **any** faithful definition of the pair — the same inventory
carries `Nat.primeCounting.eq_1` stating it verbatim, and Mathlib's own
`def primeCounting n := primeCounting' (n + 1)` makes it `rfl` there too. Both
sides delta-unfold to the same term with `n` still free.

This is ADR-1556's `Int.gcd_eq_natAbs` shape with one difference stated rather
than glossed: there a Mathlib THEOREM coincided with OUR definitional choice;
here the row is the source library's own unfolding. Declaring one of the pair
without the other opens no viable family at all (0 tens either way), so the row
cannot be avoided by declaring less. It CAN be displaced by declaring more,
which is why `Nat.lcmUpto` is part of this construction and not scope creep:
`Nat.lcmUpto_*` sorts ahead of `Nat.monotone_*` and `Nat.primeCounting_*` and
pushes the row out of the alphabetically-first ten. **8 of the 16 viable tens
carry no definitional row.** The alternative — giving `primeCounting` a
deliberately non-definitional body so the row became a genuine theorem — was
rejected as tuning the blind population.

This is also why not even the defining equations are declared. For this
construction the defining equation of the pair IS a candidate row, and a `refl`
equation about `primeCounting` under any name would put a second statement of it
into the environment. The two sibling construction files
(`count_and_div_max_pow.rs`, `factorization_lcm.rs`) omit them too.

## Blindness, before and after

`shape_search` rebuilt through `scripts/cargo-serialized.sh`; freshness
confirmed against a control that landed the same day —
`--name Rat.rank --kind definition --expect 1` returns `FOUND 1` over an index
of 3,014 declarations, matching the snapshot's own count.

Nineteen distinct candidate rows appear across the module-disjoint viable tens.
Ten are statements ABOUT `Nat.primeCounting`, `Nat.primeCounting'` or
`Nat.lcmUpto`; those constants did not exist here before this lane, so no
declaration in it could state those rows — the name query is the complete
argument for all ten rather than a proxy. Before: `--name Nat.isPrime` /
`Nat.primeCounting` / `Nat.primeCounting'` / `Nat.lcmUpto` and the
separator-insensitive `--name-like primecounting` / `--name-like lcmupto` were
all ABSENT with an `any-kind=3014` positive control on every one. After: the
four names are present as DEFINITIONS, and the check that matters is that no
THEOREM mentions them — `--const <name> --kind theorem --expect-absent` is
ABSENT for all four, each with a live `theorem=2440` positive control.

The other nine were screened by SHAPE in the kernel's own vocabulary, because
this kernel declares no `Nat.Prime`, no `Ne` and no `Nat.Coprime` and the
Mathlib spelling is unanswerable. Every query below was re-run after the
declarations landed and returned the identical count:

| candidate row | query | result |
| --- | --- | --- |
| `Int.add_two_le_iff_lt_of_even_sub`, `Int.two_le_iff_pos_of_even` | `--const Int.Even --kind theorem` | FOUND **5**, none of them either row (`even_add`, `even_add'`, `even_add_one`, `even_iff_nat_abs_even`, `ediv_two_mul_two_of_even`) |
| `Nat.ModEq.pow_totient` | `--const Nat.totient --const Nat.modEq --kind theorem` | ABSENT (control `theorem=2440 ns Nat=1078`); the Euler statement here is `Int.euler_totient_theorem`, a different carrier |
| `Nat.Prime.dvd_choose_pow`, `…_iff` | `--const Nat.choose --const Nat.dvd --kind theorem` | FOUND **1** (`Nat.prime_dvd_choose`, a prime base, not a prime POWER base) |
| `Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le` | `--const Nat.gcd --const Exists --kind theorem` | FOUND **3** (`Int.gcd_eq_gcd_ab`, `Nat.exists_mul_mod_eq_gcd`, `Nat.prime_not_coprime_iff_dvd`), none the Frobenius statement |
| `Nat.exists_base_eq_prime_pow_of_prime_pow_eq_base_pow` | `--const Nat.pow --const Exists --kind theorem` | FOUND **4**, none of them it |
| `Nat.exists_prime_gt_modEq_one` | `--const Nat.modEq --const Exists --kind theorem` | ABSENT (control `theorem=2440 ns Exists=3 Nat=1078`) |
| `Nat.exponent_dvd_of_prime_pow_eq_pow` | `--const Nat.pow --const Nat.dvd --kind theorem` | FOUND **26**, none of them `p ^ m = a ^ n → n ∣ m` |

Positive control for the vocabulary itself: `--const Nat.totient --kind theorem`
returns **19**, matching ADR-1556's independent count of the totient family.

## Evaluation table (`prime_counting_and_lcm_upto_evaluate_correctly`)

Expected values from an independent Python reference (a sieve for the prime
counts, `math.lcm` over `range(1, n + 1)`) over `n < 40`, produced before the
Rust was written. Magnitudes are deliberately tiny — every `Nat` numeral here is
unary and cost is superlinear in the largest magnitude formed.

| `Nat.isPrime` | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 9 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| | `false` | `false` | `true` | `true` | `false` | `true` | `false` | `true` | `false` |

| n | 0 | 1 | 2 | 3 | 4 | 5 | 6 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `primeCounting' n` (primes `< n`) | 0 | — | 0 | 1 | 2 | — | 3 |
| `primeCounting n` (primes `≤ n`) | 0 | 0 | 1 | 2 | 2 | 3 | — |
| `lcmUpto n` | 1 | 1 | 2 | 6 | 12 | — | — |

Four negative controls, each differing from the asserted value so none is
vacuous: `isPrime 1` must NOT be `true` (what a "no divisor strictly between 1
and n" test gives); `isPrime 9` must NOT be `true` (what a check that only tries
the divisor 2 gives); `primeCounting 2` must NOT be `0` (what `primeCounting' 2`
gives — this is the one that catches the pair being confused for each other);
`lcmUpto 4` must NOT be `24` (the product over `1 … n`, and 4 is the first
argument at which lcm and product disagree) and must NOT be `4` (a fold that
dropped its accumulator).

All four names are registered in `definition_names()` and carry an EMPTY
`axiom_footprint` — **footprint 0**, asserted in the test itself and covered by
`every_nat_declaration_is_checked_and_axiom_free`, which derives its population
from the kernel rather than a literal.

## Suite

`cargo test --release -p axeyum-lean-kernel --lib nat_prelude -- --test-threads=4`:
**400 passed, 0 failed**, 1030 filtered out of 1430. The two tests that had to
run were confirmed individually with a NONZERO count rather than inferred from
the aggregate: `prime_counting_and_lcm_upto_evaluate_correctly` (1 passed) and
`every_nat_declaration_is_checked_and_axiom_free` (1 passed).

## Did not run

`just check`, `scripts/check.sh`, `cargo test --workspace`, `cargo doc` — no
sweep was run; the touched crate was gated by the `nat_prelude` suite and by
clippy with `-D warnings`. `propose-nursery-refill.py` was not run: it screens by
module only and has neither the fact-ledger nor the `HELD_OUT_CONSTRUCTIONS` nor
the R5 screen, so it is not the candidate space this lane needed.

<!-- plan-section: landed-changes -->

| 2026-09-02 | heldout-construction-1 | ADR-1420 Route 1 executed for draw 19: four Definitions (`Nat.isPrime`, `Nat.primeCounting'`, `Nat.primeCounting`, `Nat.lcmUpto`), evaluation tests, **no theorem about any of them**; `adr-1556-draw-19-screen.py` goes exit 0 → exit **1**, `disjoint_pairs` 0 → **219**, and `modules contributing a row to EVERY viable ten` goes from the four blocking modules to **`[]`** (ADR-1559) |
| 2026-09-02 | heldout-construction-1 | the supply screen behind the choice: of 248 unowned modules **196** are topic-clean, only **five** reach `PER_FAMILY` with ≤3 added constants and **none of the five is a mathematical construction**; `Nat.centralBinom` would unlock 14 rows in one line and is refused on the path segment `Choose` alone |
| 2026-09-02 | heldout-construction-1 | found: `Nat.primeCounting_eq_primeCounting'_succ` is MATHLIB'S OWN defining equation (`Nat.primeCounting.eq_1` states it verbatim) so it is `rfl` under any faithful definition — the ADR-1556 `Int.gcd_eq_natAbs` shape on a row trivial in the source library too; declaring either half alone opens nothing, so `Nat.lcmUpto` was added to DISPLACE it and **8 of the 16 module-disjoint viable tens carry no definitional row** |
| 2026-09-02 | heldout-construction-1 | found: the committed kernel environment snapshot was **176 declarations stale**, and that staleness was silently suspending R11's environment signal — refreshing it (with NO new declarations of this lane's) turns `check-holdout-adjacency.py` red on two `disclosure` refusals whose recorded sweeps predate six `Nat.factorization*` declarations. Repaired by a real re-sweep of both reviews, with `--const Nat.factorizationLCMLeft/Right/divMaxPow --kind theorem --expect-absent` as the decisive check; verdicts unchanged, gate back to 0 refused |
| 2026-09-02 | heldout-construction-1 | found: `adr-1556-draw-19-screen.py`'s minimal-cover pruning has expired — 37 viable against the exact pass's 196, the direction ADR-1556 predicted but asserted equality on; the exact pass is the authority and the control still fires (228 viable / 1,913 pairs), so the assertion should become `pruned <= exact` |
| 2026-09-02 | heldout-construction-1 | blindness screen on all 19 candidate rows, before AND after: 10 absent because their constants did not exist, 9 screened by SHAPE in the kernel's own vocabulary with a live positive control on every query (`Int.Even` 5, `Nat.choose`+`Nat.dvd` 1, `Nat.gcd`+`Exists` 3, `Nat.pow`+`Exists` 4, `Nat.pow`+`Nat.dvd` 26, `Nat.totient` 19); after the declarations, `--const <each new name> --kind theorem` is ABSENT for all four |
