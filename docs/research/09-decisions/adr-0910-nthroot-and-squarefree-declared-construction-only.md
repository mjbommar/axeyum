# ADR-0910: `Nat.nthRoot` and `Squarefree` declared, construction-only, to unblock a future nursery draw

Status: accepted
Date: 2026-08-30
Index-summary: ADR-0762 (draw 8, declined) and ADR-0830 (draw 9, authored via
below-floor combinations that deliberately avoided the two-construction
route) both measured the same un-owned-module floor as needing
`Nat.nthRoot` AND `Squarefree` together before any NEW held-out-safe module
opens there (either alone yields zero lawful family sets; both together
yield the two `Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas` /
`Mathlib.Data.Nat.Squarefree` modules R5 needs); this lane re-verified that
measurement is still current on this tree (env=2383, same seven un-owned
modules, unchanged since ADR-0762) and then declared both constructions —
definition and evaluation test only, nothing else — closing exactly the gap
those two ADRs named and no more

Related: ADR-0762 (draw 8 declined — one constant cannot open a draw),
ADR-0830 (draw 9 authored from below-floor combinations instead), ADR-0653
(an unblocking lane declares the construction and nothing else — the
`Nat.dist` contamination this ADR is careful not to repeat), ADR-0695 (the
construction spends the closed-evaluation rows, not the evaluation test)

## Context

The brief for this lane cited an "ADR-0900 (draw 10, declined)" as
confirming this exact unblock. **That ADR does not exist in this worktree or
in `origin/main`** (`git log origin/main` tops out at the same commit as
this branch's base; `docs/research/09-decisions/` tops out at ADR-0855).
Per this repository's own rule — verify a blocker in the tree before
building against it — this lane did not inherit that citation. What IS in
the tree and independently confirms the same target:

- **ADR-0762** (draw 8, declined): enumerating the un-owned `PER_FAMILY`
  floor, `Nat.nthRoot` alone or `NatCast.natCast` alone each give **zero**
  lawful family sets; `Nat.nthRoot` **and** `Squarefree` together give
  **ten**. `NatCast.natCast` is separately rejected outright (omega
  certificate vocabulary, not mathematics).
- **ADR-0830** (draw 9, authored): re-measured the same floor
  byte-identical to ADR-0762 (`env=2383`, same seven un-owned modules) and
  chose a DIFFERENT route for that draw — combining several already-below-floor
  modules with zero new declarations — specifically to defer the
  two-construction work rather than because the measurement had changed.

Re-running the generator's own `select()`-adjacent screen on this tree
(`scripts/gen-autogenesis-nursery-refill.py`'s `admissible()`/`CONST_RE`
logic, executed in memory against the committed environment snapshot) before
writing any code:

    env=2383 admissible=2455 bridge=72 inventory=9729 owned_modules=59 PER_FAMILY=10

      26  R9 0/10  Mathlib.Data.Nat.GCD.Basic
      26  R9 1/10  Mathlib.Data.Nat.Factorial.Basic  ['Nat.ascFactorial_succ']
      21  R9 0/10  Batteries.Data.Nat.Bitwise.Lemmas
      18  R9 0/10  Mathlib.Data.Nat.Choose.Basic
      10  R9 1/10  Mathlib.Data.Int.GCD  ['Nat.gcd_eq_gcd_ab']

Five un-owned modules at the floor (two fewer than ADR-0762's seven —
`Init.Data.Nat.Bitwise.Lemmas` and `Mathlib.Data.Nat.Dist` are now owned by
draw 9's families), all five still adjacent to a published development/train
family or R9-contaminated — **zero held-out-safe, exactly as before**.
Simulating each candidate constant's admission separately confirms ADR-0762's
finding is unchanged on this tree:

    +Nat.nthRoot  only:  opens Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas (13 rows, R9 0/10) -- ONE new held-out-safe module
    +Squarefree   only:  opens Mathlib.Data.Nat.Squarefree (11 rows, R9 0/10) -- ONE new held-out-safe module
    +both together:      opens BOTH -- the two R5 needs

One alone cannot satisfy R5 (`len(new_held_out) < 2` raises); both together
can. **The enumeration ADR-0762/ADR-0830 measured still holds on this tree.**

## Decision

Declare `Nat.nthRoot` and `Squarefree` in the kernel — construction and
evaluation test, nothing else (ADR-0653). Do not touch
`artifacts/autogenesis/`, `scripts/gen-autogenesis-nursery-refill.py`, or
author a draw: this lane enables one, the next lane draws it.

### `Nat.nthRoot` — `crates/axeyum-lean-kernel/src/nat_prelude/nth_root.rs`

`Nat.nthRoot (n a : Nat) : Nat` — argument order confirmed against the
pinned inventory row for `Nat.nthRoot_zero_left` (`Lean.Expr` dump applies
`Nat.nthRoot` to `0` then `a`). By fuel-bounded **structural** linear search
(`Nat.nthRootAux (n a fuel : Nat) : Nat`), generalizing `sqrt.rs`'s existing
`sqrtAux` device (squaring, `n = 2` fixed) to an arbitrary captured exponent
`n` via `pow`, rather than reproducing Mathlib's `WellFounded.fix` Newton
iteration — the same well-founded-recursion-avoidance `sqrt.rs`/`log.rs`
already establish for this project's axiom-freedom metric. `nthRoot 0 a := 1`
by an explicit top-level branch (mandatory, not stylistic: `pow c 0 ≡ 1`
definitionally for any `c`, so an unguarded search would walk to the fuel
bound and return the wrong value whenever `a >= 1`).

### `Squarefree` — `crates/axeyum-lean-kernel/src/nat_prelude/squarefree.rs`

`Squarefree (n : Nat) : Bool` at the **bare root namespace**, not
`Nat.squarefree` — confirmed against the pinned inventory's raw `Lean.Expr`
dump, which applies the constant `` `Squarefree `` directly (Mathlib's
`Squarefree` is a root-level generic-monoid predicate, applied to `Nat` at
the use site, never spelled `Nat.Squarefree` in the statement itself).
`Bool`-valued, not `Prop`, and with no `Bool`-agrees-`Prop` bridge theorem:
a `Prop` cannot be evaluated at concrete arguments, which is what an
evaluation test needs, and a bridge is a theorem *about* the construction
that ADR-0653 says not to add here (this kernel also has no `funext`, so a
bridge would need pointwise `Bool.rec` case analysis rather than function
extensionality — machinery this file has no use for). `Nat.squarefreeAux (n
fuel : Nat) : Nat -> Bool` fuel-searches candidate divisors `k` from `2`;
`Squarefree n := if n == 0 then false else squarefreeAux n n 2`, matching
Mathlib's own `Squarefree 0 = False`.

Both reuse Mathlib names for constructions whose TYPE differs from Mathlib's
own (`nth.rs`'s precedent: `Nat.nth`, a `(Nat -> Bool) -> Nat -> Nat -> Nat`
construction under Mathlib's `(ℕ -> Prop) -> ℕ -> ℕ` name). This is
deliberate and documented in both module docs: it opens the vocabulary for
the autogenesis screen; it proves nothing about Mathlib's own construction,
and any mirror theorem stated against the real `Nat.nthRoot`/`Squarefree`
stays `open` per the mirror-flip criterion (`CLAUDE.md`).

## Verified: nothing beyond the construction and its evaluation test

Both files declare exactly two `Definition`s each (an internal `*Aux` helper
and the public construction) and **zero** `Theorem`s, `d.theorem(...)` calls,
or equation lemmas. The evaluation checks live entirely as Rust `#[test]`
functions in `nat_prelude_tests.rs`
(`nth_root_evaluates_correctly`/`squarefree_evaluates_correctly`), each
comparing `Kernel::def_eq` against independently computed values at
concrete, discriminating numerals with negative controls (off-by-one /
ceiling-vs-floor for `nthRoot`; a search that stops after one candidate, for
`Squarefree`) — no kernel declaration is claimed by either test, so neither
can ever collide with a Mathlib mirror name the way `Nat.dist`'s seven
supporting theorems did (ADR-0653).

`every_nat_declaration_is_checked_and_axiom_free`
(`nat_prelude_tests.rs`, coverage read from `kernel.environment()`, not from
a hand list) required `Nat.nthRootAux`/`Nat.nthRoot`/`Nat.squarefreeAux` to
be added to `definition_names`; `Squarefree`, at the bare root namespace,
falls outside that test's `Nat.`-prefix scope and was added anyway for
consistency with its own axiom-footprint check. `Kernel::axiom_footprint`
for all four names is the empty set (asserted directly in both new tests,
and by the pre-existing `the_nat_prelude_declares_no_axioms` sweep, which
still passes for the whole prelude with these four additions in it).

## Re-screened after declaring

Re-running the same in-memory enumeration against a fresh kernel build that
includes these four declarations (`shape_search --name-like nthRoot` /
`--name-like squarefree`, both `FOUND` with the exact expected types and
arities):

    === committed (no new constants) ===
      26  R9 0/10  Mathlib.Data.Nat.GCD.Basic
      26  R9 1/10  Mathlib.Data.Nat.Factorial.Basic
      21  R9 0/10  Batteries.Data.Nat.Bitwise.Lemmas
      18  R9 0/10  Mathlib.Data.Nat.Choose.Basic
      10  R9 1/10  Mathlib.Data.Int.GCD

    === fresh (Nat.nthRoot + Squarefree admissible) ===
      26  R9 0/10  Mathlib.Data.Nat.GCD.Basic
      26  R9 1/10  Mathlib.Data.Nat.Factorial.Basic
      21  R9 0/10  Batteries.Data.Nat.Bitwise.Lemmas
      18  R9 0/10  Mathlib.Data.Nat.Choose.Basic
      13  R9 0/10  Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas   <- NEW
      11  R9 0/10  Mathlib.Data.Nat.Squarefree                            <- NEW
      10  R9 1/10  Mathlib.Data.Int.GCD

Exactly the two new held-out-safe modules ADR-0762/ADR-0830 predicted, both
R9-clean (neither module's first ten screened rows collides with a name
this kernel already declares — the `Nat.dist` contamination check, re-run
and passing). This lane did **not** run the full `guard()`/`R5`
simulation (that requires mutating `FAMILY_MODULES`/`FAMILY_ROUTES` in
memory to author trial families, which is drawing work, not enabling work)
— the module-opening screen above is the piece this lane owns, and it
matches the prior measurement exactly.

## Holdout isolation, before and after

`python3 scripts/check-autogenesis-holdout-isolation.py`:

    AUTOGENESIS_HOLDOUT_ISOLATION|held_out=136|files_scanned=1110|settled=0|references=0|verdict=PASS

Identical before and after this lane's work — `git status` confirms zero
files touched under `artifacts/autogenesis/`, so there is nothing for this
check's inputs to have moved.

## What this does and does not unblock

This declares the two constructions the enumeration says a future draw
needs; it does not draw. The next lane still has to: regenerate
`artifacts/autogenesis/kernel-environment-snapshot-v1.json` from a fresh
kernel build (this lane deliberately did not, since that artifact is out of
this lane's scope), run the real `select()`/`guard()` end to end (not the
in-memory `admissible()` slice this ADR reports), and judge the two
"two warnings for the `Nat.nthRoot` lane" and "`Nat.nthRoot.lt_pow_go_succ_aux`
may not be a fair blind target" notes from `docs/plan/notes/383-nursery-draw-8.md`
before drawing — those are about the SHAPE of the Mathlib pool rows, not
about this lane's construction, and remain live regardless of which lane
reads them next.
