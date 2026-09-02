# `Nat.land`/`Nat.lor`/`Nat.ldiff` are recursion-principle divergences, and a blanket row is a false claim (2026-09-02)

**The named next action.** `docs/plan/status/testbit-codomain.md` measured
that `Nat.land`, `Nat.lor`, `Nat.ldiff` (and `Nat.bitwise`, which Mathlib
specializes them from) diverge from Mathlib by the same standard the
`mirror-divergence-registry` applies to `Nat.minFac`, and that none had a
registry row -- "a producer-policy decision with its own blast radius, not a
corollary of the codomain question." This lane (`divergence-bitwise`) takes
that action.

## The chain, read at the pinned commit

Mathlib v4.30 (`c5ea00351c28e24afc9f0f84379aa41082b1188f`) does not define
`land`/`lor` itself -- both are core Lean, re-exported. Core's
`Init/Data/Nat/Bitwise/Basic.lean:27` defines the general combinator:

```
def bitwise (f : Bool → Bool → Bool) (n m : Nat) : Nat :=
  if n = 0 then ... else if m = 0 then ... else
    let n' := n / 2; let m' := m / 2
    ...
    bitwise f n' m'
decreasing_by apply bitwise_rec_lemma; assumption
```

`n / 2` is not a constructor predecessor of `n`, so this needs well-founded
recursion through the equation compiler (`decreasing_by`). Line 50: `def land
: Nat → Nat → Nat := bitwise and`. Line 58: `def lor := bitwise or`. `ldiff`
is one layer further out, in Mathlib proper at
`Mathlib/Data/Nat/Bits.lean:147`: `def ldiff : ℕ → ℕ → ℕ := bitwise fun a b
=> a && not b`.

This kernel's `nat_prelude/land.rs`, `lor.rs`, `ldiff.rs` each land their
operator as an **independent structural fuel recursion** --
`declare_land_all` (land.rs:90-190), `declare_lor_all` (lor.rs:113-217),
`declare_ldiff_all` (ldiff.rs:120-228) -- not as a specialization of any
shared combinator. `land.rs`'s own module doc (top of file, unchanged since
it was written) already states why: Mathlib's `bitwise` "recurses on neither
argument structurally ... and needs well-founded recursion -- through the
equation compiler, `Quot.sound`/`propext`, fatal to this project's
axiom-freedom metric." `nat_prelude/bitwise.rs` (`declare_bitwise_all`,
lines 339-482) later lands a general two-argument combinator too, but its
own module doc says it is landed "by the same structural fuel-recursion
device" as the other three -- never Mathlib's well-founded one.

So the divergence is in the **recursion principle** (fuel vs. well-founded),
the same class ADR-0840 already applies to `Nat.fastFib`/`binaryRec`, not an
`algorithmic` divergence (same values, different search, `Nat.minFac`'s
class) and not a `definitional` one (different function altogether,
`Nat.multichoose`'s class).

## Why this is NOT a blanket row

A naive registration was tried and measured, not assumed. Adding

```json
{"mathlib_constant": "Nat.land", "surface_forms": ["&&&"], "class": "recursion-principle", ...}
```

and running `python3 scripts/check-dispatchable-frontier.py` fails
immediately:

```
FAIL: G3 blocks-a-settled-mirror: Nat.land would block 13 already-settled
mirror(s): F:ml430-nat-and-assoc-273b60d8, F:ml430-nat-and-comm-7525d05a,
F:ml430-nat-and-div-two-1a2f7c33, F:ml430-nat-and-le-left-6d04acb7,
F:ml430-nat-and-le-right-a3f80076. A construction we have closed a mirror
over does not diverge.
```

A `Nat.bitwise` row with `surface_forms: ["Nat.bitwise"]` fails the same
guard against its own 3 mirrors (`bitwise-bit`, `bitwise-comm`,
`bitwise-swap`, all `proved`), and additionally matches **zero** open
mirrors (no currently-open `ml430` fact writes `Nat.bitwise` as a literal
identifier -- Lean's pretty-printer always renders `land`/`lor` via
`&&&`/`|||` notation), so it is doubly wrong: G1-stale on the open side, G3
false-positive on the closed side. **`Nat.bitwise` is left unregistered as
its own row** -- this is the same "over-blocking direction" caught for
`Max.max`/`Min.min` in
`docs/research/11-design-review/2026-09-01-divergence-registry-gaps-closed.md`,
now measured for a second construction family.

The reason 15 mirrors over `land`/`lor`/`ldiff` are already closed despite
the recursion-principle divergence: this kernel's own bridge theorems
(`Nat.bitwise_and_eq_land`/`Nat.bitwise_or_eq_lor`,
`nat_prelude/rec_agreement.rs:403-411`, universal over symbolic `m`/`n`)
reconcile its fuel-based `bitwise` and its fuel-based `land`/`lor` well
enough that algebraic-law mirrors (`comm`, `assoc`, `self`, `le_left`,
`le_right`, `div_two`, `mod_two_eq_one`, `one_is_mod`, `or_distrib_left`,
`or_distrib_right`, `bit`) close by an INDEPENDENT route that never needs
Mathlib's well-founded recursion. `land_comm`'s own evidence record says so
explicitly: the route taken is "NOT Mathlib's own route via `bitwise_comm`"
(`nat_prelude/rec_agreement.rs:1654-1657`). Per the registry's own guard
philosophy -- "a construction we have closed a mirror over does not
diverge" -- a blanket row would be a false claim about this construction, not
merely an over-cautious one.

## What was registered instead

Three rows, `class: recursion-principle`, each with a `surface_forms` entry
that targets exactly the shape that is *actually* unclosed: the operator
composed immediately with `.testBit` --

| construction | surface form | blocks |
| --- | --- | --- |
| `Nat.land` | `"&&& n).testBit"` | `F:ml430-nat-testbit-land-dfef7ca4` |
| `Nat.lor` | `"\|\|\| n).testBit"` | `F:ml430-nat-testbit-lor-7644e067` |
| `Nat.ldiff` | `".ldiff n).testBit"` | `F:ml430-nat-testbit-ldiff-16f94162` |

The argument names (`m n k`) match Mathlib's own pinned declarations
verbatim (`Mathlib/Data/Nat/Bitwise.lean:115` `testBit_lor`, `:118`
`testBit_land`, `:122` `testBit_ldiff`), which this project's statement
generator extracts from Mathlib source rather than inventing, so the surface
form is not tied to an accident of one lane's variable-naming choice.

**All three targets were already `DIVERGENCE-BLOCKED` before this change**,
via the pre-existing `Nat.testBit` row's `"testBit"` surface form (that row's
own `why` field already narrates this exact chain, item 3). No fact moved
buckets. The value of these three rows is: (1) an independent, second reason
each of the three composite mirrors cannot close -- not merely that
`testBit`'s codomain differs, but that closing them via the `land`/`lor`/
`ldiff` argument would ALSO need Mathlib's specific well-founded `bitwise`
machinery; (2) `check-dispatchable-frontier.py`'s G3 false-positive control
now also fires if any of these three specific mirrors is (mis)closed; (3)
`--screen`/`--statable` now reject a future preregistration candidate of
this exact composite shape before it enters the nursery.

## Verified

`python3 scripts/check-dispatchable-frontier.py`: G1/G2/G3/G5 all pass for
the 3 new rows (checked by running with each row individually, then all
three together, then reverting to the pre-existing 9-row registry as a
before/after diff). The pre-existing `G7 queue-below-floor` failure (2
dispatchable against a floor of 10) is unrelated -- unchanged before and
after, confirmed on `main` prior to this lane by `testbit-codomain`'s own
status note.

Frontier counts, `python3 scripts/check-dispatchable-frontier.py --json`
(registry swapped back and forth for the same fact/nursery snapshot):

|  | before (9 constructions) | after (12 constructions) |
| --- | --- | --- |
| registered constructions | 9 | 12 |
| `blocked` bucket | 12 | 12 |
| `dispatchable` bucket | 2 | 2 |
| `held_out` bucket | 195 | 195 |
| `mutation` bucket | 12 | 12 |
| `open_mirrors` (total) | 221 | 221 |
| `guard_failures` | 1 (pre-existing G7) | 1 (same pre-existing G7) |

No mirror moved buckets. This is the expected, honest outcome: the
`Nat.testBit` row already carried this chain in prose; these three rows make
it a second, independently-checkable registry entry rather than only a
paragraph inside a different construction's `why` field.
