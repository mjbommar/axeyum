# 345 — nursery draw 6


## Status

LANDED as a **decline**. No draw was authored. ADR-0620 predicted draw 6
could not satisfy R5; measured, it is worse than predicted — **zero**
coherent held-out-safe families exist, not one. The finding, the three
corrections to ADR-0620 and the two named unblocks are
[ADR-0645](../../research/09-decisions/adr-0645-draw-6-is-declined-there-is-no-held-out-safe-family-left.md).

`FAMILY_MODULES` and `FAMILY_ROUTES` are unchanged, `nursery-v1.json` and
`nursery-v2-extension.json` are untouched, no row moved partition, and no
attestation count was raised.

## Was an honest draw possible? No, and here is the arithmetic

R5 is hard-coded (`len(new_held_out) < 2` raises), `PER_FAMILY = 10` is a
literal, and the cycle assigns the first new family to held-out, so **any
draw needs 20 held-out-safe rows in two coherent families**.

| | rows |
| --- | --- |
| drawable, generator screens | 2,155 across 88 modules |
| in modules an existing family OWNS — unreachable | 1,716 |
| in UN-OWNED modules | 439 across 58 modules |
| un-owned modules at or above the floor of 10 | **11**, all over published math |
| un-owned, sub-floor, adjacent only to held-out or nothing | **7**, and not one question |

Seven against a required twenty. The seven are Int `emod` boundary (2),
sums of two squares (1), an nth-root bound (1), non-existence of a square
(1), monotone stabilisation (1) and a `Nat` existence lemma (1) — six
different questions, so they do not form even one family.

## The eleven ready modules, and why none may be blind

Every one sits over mathematics an existing development or train family
already publishes — draws 2–5's exclusion list, now complete:
`Nat.Prime.Basic` 48 and `Nat.Prime.Defs` 29 (natural-primes, development),
`Nat.GCD.Basic` 44 (natural-gcd, development), `Nat.Factorial.Basic` 40
(natural-factorial, train), `Nat.Choose.Basic` 34 (natural-binomial,
development), `Init…Nat.Bitwise.Lemmas` 33 / `Batteries…Bitwise.Lemmas` 21 /
`Nat.Bitwise` 18 (natural-bitwise, development), `Nat.Fib.Basic` 22
(natural-fibonacci, train), `Int.Fib.Basic` 21 (integer-fibonacci, train),
`Int.GCD` 20 (integer-gcd, train). All eleven stay fine for
development/train, where nothing is blind.

## The two discrepancies draw 5 flagged — both still hold, and there is a third

1. **A module belongs to exactly one family.** `select`'s `module_family` is
   a flat dict comprehension, confirmed by reading it. 39 modules are owned
   and hold **1,716** drawable rows that no new family can reach.
2. **`HELD_OUT_CONSTRUCTIONS` is applied by the generator and not the
   proposer.** Still fires: `Mathlib.Data.Nat.Log` 36 → **0**. One
   correction — `Mathlib.Data.Nat.Sqrt` is 24 → **1**, not the zero draw 5
   reports, because `Nat.not_exists_sq` mentions no screened construction.
3. **NEW — the two scripts also carry different HYGIENE regexes.** The
   generator additionally drops `\.inj$`, `\.injEq$`, `\.noConfusion` and
   `^Int\.Linear\.`/`^Nat\.Linear\.`; the proposer does not. This collapses
   `Init.Data.Int.Basic` 10 → **6** and `Init.Data.Int.Linear` 10 → **2**.

   That third one is what actually decided this draw. `Init.Data.Int.Basic`
   is the only un-owned floor-height module whose mathematics is unpublished
   (natCast bridging, beside the held-out `integer-natcast`) — under the
   proposer's screen it is exactly the held-out family draw 6 needed, and
   under the generator's it does not exist. **So the drawable ready set is
   11, not the proposer's 15 and not ADR-0620's 13.**

## Screens run on the one family that looked drawable

`Init.Data.Int.Basic`, before the hygiene divergence ruled it out:

- **Name screen (R9)** — `source_name in kernel-environment-snapshot`:
  **0 of 10** contaminated.
- **Type screen** — the brief's own warning is that a name screen is
  structurally blind to a proposition proved under a different name
  (`F:ml430-nat-dvd-mul-right` was satisfied by `Nat.dvd_mul`). Ran
  `int_theorem_inventory` (232 rendered Int-prelude types) and searched for
  each candidate's shape: **0 of 10** matched, with a positive control (232
  theorem rows present) in the same command.

  Two honest caveats, both in the direction that makes this an
  over-estimate of safety: the prebuilt binary is stamped 04:02 and predates
  the 05:12 merge, so it cannot see today's declarations; and a theorem
  inventory lists theorems, not definitions, so `Int.ofNat.inj`-style
  constructor facts available definitionally would not appear. Neither
  changes the outcome — the family fails on supply, at 6 rows against 10.

## `instSubNat` is the wrong lever, measured

ADR-0620 names it the cheapest route because it sole-blocks 292 rows (290 on
this run). Re-running the screens with each constant admissible and counting
un-owned modules that CROSS the floor:

| declared | drawable | un-owned ready | newly opened |
| --- | --- | --- | --- |
| baseline | 2,155 | 11 | — |
| `instSubNat` | 2,440 | 11 | **0** |
| `Int.lcm` / `Int.bmod` / `Int.fdiv`+`fmod` / `Int.tdiv`+`tmod` / `Int.sign` | 2,189–2,272 | 11 | 0 each |
| **`Nat.dist`** | 2,173 | 12 | `Mathlib.Data.Nat.Dist` (**18**) |
| **`Nat.nth`** | 2,173 | 12 | `Mathlib.Data.Nat.Nth` (**11**) |

`instSubNat` adds 285 drawable rows and every one lands in a module already
owned or already ready. It is the biggest lever on *dispatchable* supply and
worth exactly nothing to blind breadth.

**`Nat.dist` + `Nat.nth` are precisely the two held-out families R5 needs**
— 18 and 11 rows, R9 name screen 0 of 18 and 0 of 11, each one coherent
question, neither named by any existing family. Both counts verified under
the generator's hygiene, not the proposer's.

## A live defect that blocks the NEXT draw too

`gen-autogenesis-nursery-refill.py --check` is **RED on `main`**, and not
because of anything here — my worktree's copy of the file is byte-identical
to HEAD and the generator does not read anything I edited.

`mathlib-statable-vocabulary-v1.json` has **two writers**. `bridge` (72) and
`settled` are identical between them; only the newer
`gen-autogenesis-statable-vocabulary.py` emits `bridge_provenance` and
`row_digest`. Draw 5 landed 01:49 with this check green; `edd775b19` landed
04:23 and made the refill generator's copy stale.

The trap is the error message's own advice — "regenerate without `--check`",
which is what authoring a draw does, would **delete `bridge_provenance` and
`row_digest`** inside a commit that looks like a draw.
`gen-autogenesis-statable-vocabulary.py --write` says `UNCHANGED`, so the
routine repair does not fix it and gives no warning. **I did not run the
refill generator without `--check`.**

## Verification — every command run in the foreground

| check | before | after |
| --- | --- | --- |
| `check-dispatchable-frontier.py` | exit 0, dispatchable **12**, floor 10 | exit 0, dispatchable **12** (unchanged — nothing drawn) |
| `check-autogenesis-holdout-isolation.py` | `held_out=116 files_scanned=1107 settled=0 references=0 PASS`, exit 0 | identical, exit 0 |
| `gen-autogenesis-nursery-refill.py --check` | RED (vocabulary stale) — pre-existing since 04:23 | RED, same message, unchanged |
| `gen-autogenesis-statable-vocabulary.py --write` | — | `UNCHANGED`, exit 0 |
| `propose-nursery-refill.py --remeasure` | — | exit 0, 2,237 survivors, 15 ready (11 drawable) |
| `validate-facts.py` | — | see below |
| `gen-adr-index.py` | — | see below |
| `gen-plan.py` | — | see below |
| `check-merge-hygiene.sh` | — | see below |

The brief's premise was one row stale: it quoted **13** dispatchable and the
measurement on arrival, after merging local main, was **12**.

## `check-fast.sh`: 25 failures, and none of them is mine

`bash scripts/check-fast.sh` exits 1 in this worktree with 25 FAILED steps.
Rather than assume they were inherited, I baselined: `scripts/
lane-snapshot.sh ac8120391` (the commit this lane merged from) and ran the
same gate there.

| | failures |
| --- | --- |
| baseline `ac8120391` | **62** |
| this worktree | **25** |
| in mine and NOT in the baseline | **0** |

Zero. Nothing in this lane broke a gate. The baseline's extra 37 are
snapshot-environment artifacts — steps needing a built `target/` or git
history that a `git archive` extraction does not have — plus two that this
lane genuinely REPAIRED: `propose-nursery-refill` and its test suite fail at
the baseline on a stale `refill-headroom-v1.json` and pass here, because
`--remeasure` refreshed it. Confirmed directly, exit 0.

`plan-authority` deserves separate mention: it caps a status file at 3,000
bytes and is red for **211** pre-existing files, draw 5's own
`325-nursery-draw.md` among them. My first draft added a 212th; the detail
moved here and the status doc is now 2,984 bytes. Verified both directions
— 212 → 211, mine gone, the 325 control still firing in the same run.
`scripts/archive-plan-status.py --apply`, which the error message
recommends, has **no path scoping** and would rewrite all 212, sweeping
every other lane's status docs. Not run.

## The proposer gate is green and its advice cannot be followed

`propose-nursery-refill.py` exits 0 saying:

> OK -- 15 ready family(ies) available, enough for a draw of 2 that clears
> the floor of 10. Author it in gen-autogenesis-nursery-refill.py's
> FAMILY_MODULES and FAMILY_ROUTES, then re-run the generator.

Every clause is wrong for the purpose a lane reads it for. The drawable
ready set is 11, not 15; a draw of 2 needs one held-out family and none
exists; and "re-run the generator" is the command that would delete
`bridge_provenance`. A lane that follows this output exactly will produce
either a `RefillError` or a silent revert. That is the same
checker-that-cannot-fail shape this repository keeps finding, arriving as a
green gate giving confident instructions.

## Next

- **Decide which generator owns `mathlib-statable-vocabulary-v1.json`**
  before anyone authors a draw. This is the blocking item.
- **Declare `Nat.dist`**, then `Nat.nth`. That is the whole unblock, and it
  is ordinary proof work in `nat_prelude`. `Nat.dist a b = (a - b) + (b - a)`
  is close to free; `Nat.nth` needs `WellFounded.fix`, which this kernel has.
  Declaring them requires regenerating
  `kernel-environment-snapshot-v1.json`, which needs a kernel build.
- Do **not** reach for `instSubNat` to fix the queue's blind half; it is
  measured at zero there. It remains the right lever for dispatchable rows.
- Consider whether the proposer should simply import the generator's
  `HYGIENE` and `HELD_OUT_CONSTRUCTIONS` rather than carrying its own
  copies. Three divergences have now been found between them, each
  over-reporting readiness, and each cost a lane real time.
- `check-autogenesis-nursery.py` is still red on main (draw 5's finding,
  development ↔ train dependency edges). Not touched here.
