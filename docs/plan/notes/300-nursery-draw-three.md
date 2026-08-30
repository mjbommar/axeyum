# Notes: 300-nursery-draw-three

Detail moved out of [`../status/300-nursery-draw-three.md`](../status/300-nursery-draw-three.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**Round 1** repeated draw 2's exact judgement rule ("every adjacency lands in
the same partition") and picked three modules with **no existing nursery-family
adjacency at all** -- `Init.Data.Nat.Basic`/`Init.Data.Nat.Lemmas` (plain Nat
add/order algebra), `Init.Data.Int.Lemmas` (the Int analogue), `Init.Prelude`
(Nat order/comparison bridging, screened) -- plus `Mathlib.Data.Int.Init`,
whose first 10 screened candidates are purely `Int.div_*`/`Int.dvd_*`
inequalities, adjacent to the ALREADY held-out `integer-division` (v2) --
blind beside blind, the `natural-induction-and-divisibility` precedent from
draw 2. Module-path sort put two of these at the held-out slots.

Running the generator refused it:

```
autogenesis-nursery-refill: R9 3 held-out candidate(s) already have a
declaration of the same Mathlib name in the kernel environment, so they are
not blind: [('integer-basic-arithmetic', 'Int.add_assoc'),
            ('integer-basic-arithmetic', 'Int.add_comm'),
            ('integer-basic-arithmetic', 'Int.add_neg_cancel_right')]
```

**The finding worth keeping: "no nursery family covers this math" and "this
kernel has never proved it" are different claims, and basic algebra satisfies
the first and fails the second.** Checked directly (not just the one family
R9 named first) -- `natural-basic-arithmetic`'s first 10 also collide 3/10
(`Nat.add_assoc`, `Nat.add_comm`, `Nat.add_eq_zero`), and `Init.Prelude`'s
collide **9/10** (`Nat.le_antisymm`, `Nat.le_refl`, `Nat.ble_*`, ...). A
nursery family's absence measures Mathlib's directory structure against our
own family list; it says nothing about whether `nat_prelude`/`int_prelude`
already cover the ground, and for genuinely foundational algebra they almost
always do. This is the SAME shape as the "empty result from a tool never
pointed at your subject" trap, arriving from the opposite direction: a
correctly-computed non-adjacency was mistaken for non-existence.

**Round 2** kept the two contaminated-but-harmless novel families for
DEVELOPMENT/TRAIN (contamination there is a feature -- fast closure -- not a
defect) and searched for a SECOND held-out-safe candidate that is both
adjacency-clean and R9-clean. `Mathlib.Data.Int.Init` alone survives from
round 1. Combining `Init.Data.Int.DivMod.Basic` (7 screened: ediv/emod
boundary-case lemmas) with `Mathlib.Data.Int.Basic` (8 screened: dvd/natCast
lemmas plus one `gcd_emod`) reaches 15 total, first 10 overwhelmingly
div/dvd/ediv/natCast, **zero of which collide with a kernel declaration** --
checked, not assumed:

```
integer-division-boundary-cases contaminated: 0 []
integer-division-inequalities   contaminated: 0 []
integer-basic-arithmetic        contaminated: 3 (fine -- development, not held-out)
natural-basic-arithmetic        contaminated: 3 (fine -- train, not held-out)
```

Module-path sort:

    Init.Data.Int.DivMod.Basic  (integer-division-boundary-cases)   held-out
    Init.Data.Int.Lemmas        (integer-basic-arithmetic)          development
    Init.Data.Nat.Basic         (natural-basic-arithmetic)          train
    Mathlib.Data.Int.Init       (integer-division-inequalities)     held-out

Two NEW held-out families (R5), both R9-clean, both matching their one
adjacency exactly (blind beside blind, same as draw 2's
`natural-induction-and-divisibility`). No target outcome was consulted for
the ASSIGNMENT -- the cycle produced exactly this from the module-path sort;
what was chosen by judgement is the SET, same as draw 2.

`Mathlib.Data.Nat.ModEq`, `*.Gcd`, `*.Prime.*`, `*.Factorial.*`,
`*.Choose.*`, `*.Bitwise.*` remain excluded for the same reason draw 2 gave --
each adjacent to a v1 family that is development or train (published), so a
held-out assignment there would be the `natural-division` violation
regardless of R9 (R9 only catches EXACT name collisions; the broader
technique-leakage risk the ADR describes is a judgement call R9 cannot see,
and does not need to fire for the exclusion to hold).

## Already-proved fraction

```
python3 scripts/check-autogenesis-already-proved.py
screened: 28
already NAME-MATCHED in the kernel environment: 6 (21.4%)
  Int.add_assoc, Int.add_comm, Int.add_neg_cancel_right,
  Nat.add_assoc, Nat.add_comm, Nat.add_eq_zero
```

All 6 matches are in the two novel dev/train families, consistent with the
round-1 R9 measurement (30% of THOSE 20 rows collide by name). The 8
pre-existing totient/coprimality rows remain 0% matched, unchanged from
draw 2's measurement. A name match is necessary, not sufficient, for
"already proved" -- confirm the rendered type via `nat_theorem_inventory`
against `formal.statement` before flipping any fact's status.

## Checks (all foreground)

| check | result |
| --- | --- |
| `check-autogenesis-holdout-isolation.py` **BEFORE** | `held_out=87\|files_scanned=1105\|settled=0\|references=0\|PASS` |
| `check-autogenesis-holdout-isolation.py` **AFTER** | `held_out=107\|files_scanned=1105\|settled=0\|references=0\|PASS` |
| `check-dispatchable-frontier.py` | exit 0, **DISPATCHABLE 28** (was 8) |
| `check-autogenesis-already-proved.py` | exit 0, 28 screened, 6 matched (21.4%) |
| `validate-facts.py` | exit 0, 2114 facts, 0 errors (161 open, +40) |
| `check-fact-depends-derived.py` | exit 0, `missing_edges=0` |
| `create-autogenesis-chain-catalog.py --check` | exit 0, `edges=11827` |
| `scripts/tests/test-dispatchable-frontier.sh` | 25/25 |
| `gen-plan.py --check` | exit 0 (no lane-status edits pending regeneration -- this file plus this run) |
| `gen-autogenesis-nursery-refill.py --check` | exit 1 (pre-existing, see below -- NOT introduced by this draw) |

Every check run bare with exit code captured separately (not through a
pipeline), per the repository's own banned-idiom list.

## Found and NOT repaired here (owed elsewhere, per the brief's scope)

**Preregistration drift is now 3 files, not draw 2's 1.** `--check` printed:

```
F-ml430-nat-dvd-two-of-totient-le-one-3642bf31.json  -- formal.language, formal.statement
F-ml430-nat-totient-eq-one-iff-68d883a0.json         -- formal.language, formal.statement
F-ml430-nat-totient-eq-zero-3be161d6.json            -- statement
```

The third is the SAME fact draw 2 already flagged (`nat-totient-eq-zero`,
kernel-rendered `AxNat` type replacing the `lean4-surface` original). The
other two are new since then -- both in the totient family lanes closed this
session. This is a real, growing pattern (surface-statement rewrites landing
alongside a proof) and is out of scope for a nursery draw to fix: the brief's
non-negotiable is not to touch existing entries' partitions, and repairing a
drifted `formal.statement` is a different, larger question (whether the
rewrite is itself honest) that belongs to whoever owns the totient lane.
`gen-autogenesis-nursery-refill.py --check` stays unregistered in `check.sh`/
the justfile for the same reason draw 2 left it that way.

**The `natural-divisibility` amendment is still owed.** Unchanged from draw 2:
4 of 10 held-out rows in that family already have same-named kernel
declarations, pre-dating R9. `held_out=107` overstates blind breadth by up to
10 of those rows until an ADR-0542 amendment lands.

## Next

Dispatchable is 28, and 21.4% of the new supply is free by name match (confirm
before flipping). 16 families now exist across v1+v2; the quoted cohort is 160
of 214 -- 54 rows of headroom remain for a fourth draw, though genuinely novel
held-out-safe supply (adjacency-clean AND R9-clean) is now down to the two
families used here plus whatever remains unexplored in `Mathlib.Data.Int.Init`
and its DivMod.Basic/Basic combination beyond the first 10 each.
