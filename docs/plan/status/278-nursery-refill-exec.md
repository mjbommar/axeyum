# Lane: nursery-refill-exec -- the positive "statable here" screen, and the refill

<!-- plan-section: lane-status -->

**Your lane's block (`IN PROGRESS (statable-here screen measured; refill in
progress)`, nursery-refill-exec, 2026-08-29).**

WORK IN PROGRESS -- this file is committed early, per the brief's
first-commit-within-ten-tool-calls rule, so that a stall leaves the measurement
behind rather than nothing.

---

## Step 0 -- re-measurement

`scripts/check-dispatchable-frontier.py` is **red on `main`**, as briefed, and
the number is one lower than the previous lane recorded (a mirror closed in
between):

```
FAIL: G4 empty-dispatchable-set
open ml430 mirrors: 58
  held-out (blind evaluation, do not dispatch): 35
  mutation negative controls (never closable):  12
  structurally blocked by a divergence:         11
  DISPATCHABLE:                                 0
```

`scripts/check-autogenesis-holdout-isolation.py` **before**:

```
AUTOGENESIS_HOLDOUT_ISOLATION|held_out=37|files_scanned=1103|settled=0|references=0|verdict=PASS
```

### One correction to the previous lane's record

`docs/plan/status/275-autogenesis-refill.md` names the pinned statement source
as `mathlib-v4.30.0-nat-int-statement-inventory-v1.ndjson`. **The pinned
artifact is `-v2`**, and the two are different files:

| file | sha256 | pinned by |
| --- | --- | --- |
| `…-inventory-v1.ndjson` | `b3569d54…` | nothing in the tree |
| `…-inventory-v2.ndjson` | `4285e551…` | ADR-0479, `mathlib-statement-source-v1.json`, and 15 scripts |

Both carry 9,729 records, which is why the substitution is invisible from a
record count. This lane reads **v2**, the pinned one.

---

## (1) The positive "statable here" screen

### The idea

The divergence registry is a **negative** screen: it names constructions whose
axeyum counterpart diverges and blocks mirrors over them. It says nothing about
whether a proposition can be *expressed* here at all, which is why 843
`Range.Polymorphic` and 174 `Floor.Ring` rows pass it.

The positive screen asks the complementary question, and it is answered from
the **kernel environment**, not from a theorem inventory (which lists no
`Definition`s -- `Nat.add` returns zero rows from
`prelude_theorem_inventory` and certainly exists).

A pinned Mathlib statement's `type_repr` is a structural `Lean.Expr` dump, so
the exact set of Lean constants it mentions is extractable mechanically:

```
Lean.Expr.const `Nat.fib []   ->   Nat.fib
```

A candidate is **statable here** iff every constant in its type is admissible,
where the admissible vocabulary is

```
  env      2,207 declaration names read from kernel.environment()
           (shape_search --include-constructed, all six populated kinds)
+ bridge      70 Lean surface constants that are NOT in the environment but
           appear in the pinned statement of a mirror we have ALREADY CLOSED
```

The bridge is **derived, never asserted**. It is exactly
`{constants of settled ml430 mirrors} \ env`, so an entry exists only because
the ledger closed a mirror stated with it. That covers three things the kernel
does not name and does not need to:

- typeclass/notation elaboration -- `HAdd.hAdd`, `instHAdd`, `OfNat.ofNat`,
  `LE.le`, `instLENat`, `Dvd.dvd`, `Nat.cast`;
- Mathlib abbreviations that unfold into the kernel's vocabulary --
  `Nat.Coprime` (`gcd a b = 1`), `Nat.ModEq` (`a % n = b % n`), `Nat.Prime`,
  `Even`, `Odd`, `ite`;
- order abbreviations that unfold the same way -- `Monotone`, `StrictMono`,
  `StrictMonoOn`, `Set.Ici`, `Symmetric`, `Function.swap`.

Every one of those is witnessed by a closed mirror. `Nat.fib_strictMonoOn`, for
instance, is `proved` with the kernel type
`2 <= a -> 2 <= b -> a < b -> fib a < fib b` -- `Set.Ici 2` unwound to two
explicit bounds. That is what "bridge" means here: the surface constant has no
kernel counterpart and needs none.

### The surviving count

```
pinned theorem records                                    9,729
after dropping compiler-generated / hygienic names        9,134
already in the ml430 catalog                                202
unused supply                                             8,932
  of which STATABLE HERE                                  2,773   (31.0%)
```

**The screen is not vacuous: it rejects 6,159 of 8,932 (69.0%).** The
constants doing the rejecting are exactly the structures the previous lane
predicted, now counted rather than inferred:

```
  631  instSubNat                     (Int subtraction instance -- not the Nat one)
  582  List
  498  Std.PRange.instUpwardEnumerableNat
  471  Lattice.toSemilatticeInf
  428  Membership.mem
  381  LinearOrder
  377  Finset
  369  Array
  363  MulZeroClass.toZero
  323  Std.PRange.instUpwardEnumerableInt
  263  Set
  217  Ring
```

### It is also not a false-positive machine

**Every one of the 156 settled `ml430` mirrors passes the screen.** That is the
G3-shaped control the existing gate already uses -- run against the real
population on every invocation, not against a fixture.

### Where the survivors are

```
  335  Init.Data.Int.Order              91  Mathlib.Data.Nat.ModEq
  252  Init.Data.Nat.Lemmas             87  Mathlib.Data.Int.ModEq
  216  Init.Data.Int.DivMod.Lemmas      84  Init.Data.Nat.Gcd
  204  Init.Data.Nat.Basic              64  Init.Data.Nat.Lcm
  149  Init.Data.Int.Lemmas             55  Mathlib.Data.Nat.Prime.Defs
  121  Init.Data.Int.Gcd                51  Init.Data.Nat.Bitwise.Lemmas
```

Those map onto families the split policy already has (`natural-gcd`,
`natural-primes`, `natural-bitwise`, `natural-modular-equivalence`,
`integer-gcd`, `integer-modular-equivalence`) plus at least two it does not
(integer order, integer division/modulo).

**Supply is not the binding constraint.** The remainder of this lane is about
the constraints on preregistering, which are.

---

## (2) Preregistration -- IN PROGRESS

## (3) Gate verdict -- IN PROGRESS
