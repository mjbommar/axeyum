# Lane: score-the-blind-population — cash the held-out partition for the first time

<!-- plan-section: lane-status -->

**Lane block (`DONE`, score-the-blind-population, 2026-09-01).** The held-out
partition had never been scored: 176 proved in development, 125 in train,
**0 of 190 held-out**. Not a failure — `check-autogenesis-holdout-isolation.py`
made every route to a recorded score a gate breach, so a population built to be
scored could not be. ADR-1480 amends that: a settled held-out fact is permitted
**only** when a committed evaluation record names it and that record carries the
`protocol_commit` that fixed the protocol before the outcomes. Six new guards,
each mutation-verified to be killed by a test only it kills.

**Score: 10 CLOSED of m = 10** on `integer-absolute-value`, selected by a rule
committed at `067d675a3` before any statement was read; every row admitted first
attempt, axiom-free. **Do not quote 10/10 as a rate.** The family was cheap for
one structural reason — `Int.le`/`Int.lt`/`Int.mul` are four-case COMPUTING
definitions here, so after an `Int.rec` split every goal has already ι-reduced
and a sign hypothesis is self-discharging in the branches it excludes. Mathlib
proves the same ten through `abs` and the ordered-ring API; the routes share
nothing. A family whose content is not constructor-shaped gets none of this.

**Next lane should take a family that is NOT constructor-shaped**, or the second
measurement inherits this one's bias instead of testing it. Seventeen of the
nineteen held-out families remain fully blind; the eighteenth
(`descent-and-well-ordering`) carries a disclosed one-row statement exposure and
was excluded by the selection rule rather than scored.

**Two findings that are not the score.**
(1) `every_int_declaration_is_checked_and_axiom_free` scopes itself
`starts_with("Int.")`, so **13 `Nat.`-namespace theorems declared from the Int
prelude had no axiom-freedom check from anywhere** — ten of them pre-existing,
including `wilson.rs`'s whole `Nat.inverseIndex` family, `Nat.gcd_eq_gcd_ab` and
`Nat.xgcdAux_sound`. Closed by an environment-derived assertion with a
non-vacuity guard.
(2) The `held_out=186` pin in `test_check_autogenesis_holdout_isolation.py` —
the gate whose job is to notice a partition moving — was **red on `main` and
nobody had run it**; draw 18 added two families and did not move it. Established
(not transcribed) and moved to 206.

**Left open on purpose.** A scored row's dependency component crosses
partitions, and `validate_exemptions` refuses any exemption naming a held-out
row with no branch for a scored one. Measured: `check-autogenesis-nursery.py` is
**already red on `main`** (verified in a detached worktree at `7e2f859dc`, same
3 violation types, 5 components, 302 rows); the scoring adds **no new violation
type and no new leaking component**, only 5 more listed rows in a component that
was already leaking. An amendment excluding scored rows was written and
**reverted** after being measured as a byte-identical no-op — shipping an
unexercised widening of a blindness guard is the failure this repository cares
most about, arriving in the direction nobody watches. ADR-1480 hands the
decision to whoever has a crossing whose verdict depends on it.

<!-- plan-section: landed-changes -->

| 2026-09-01 | `067d675a3` | Pre-registered the scoring protocol BEFORE reading any target, plus `check-drawn-population-zero-diff.py` (716 drawn rows digested; its negative control — flip one partition, require the digest to move — runs on every invocation). |
| 2026-09-01 | `53a0065d2` | 4 of 10: the `natAbs_inj_of_*` mirrors, first attempt each. Three of four branches close on the sign hypothesis alone, because `Int.le Int.zero (negSucc n)` IS `False`. |
| 2026-09-01 | `ce3a4cbac` | 5 more: the `mul_self` cluster (3 new `Nat` squaring lemmas carry all its content) and the `coe_sub_coe` pair (`subNatNat_elim` after the `ofNat_add_negOfNat` bridge — the two stuck terms are NOT defeq). Plus the `Nat.`-namespace axiom-freedom gap, 13 declarations. |
| 2026-09-01 | `32e338978` | Row 1, `natAbs_emod_two`: the family scores **10 of 10**. Its two parity cases take different routes — there is no `Nat.odd_iff_even_succ` to mirror `even_iff_odd_succ` with. |
