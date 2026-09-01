# A growing divergence registry breaks historical draws

**Bisected 2026-09-01.** `scripts/gen-autogenesis-nursery-refill.py --check`
is **red on `main`**:

```
a3da5621c~1   EXIT 0   AUTOGENESIS_NURSERY_REFILL_OK|entries=460|...
a3da5621c     EXIT 1   family 'natural-find-greatest' yields 0 screened
                       candidates, fewer than the 10 the refill takes
```

`a3da5621c` is the divergence-registry sweep (ADR-1415). It registered five
constructions — `Squarefree`, `Nat.nth`, `Nat.findGreatest`, `Nat.floorRoot`,
`Nat.ceilRoot` — every one of them correctly, against Mathlib's actual source
at the pinned commit. Three **already-drawn** families then fell under the
ten-candidate floor: `natural-find-greatest`, `natural-integer-root`,
`natural-nth-selector`. For `Data.Nat.Find` the screen reports 17 rows blocked
on `Nat.find` and **15 blocked by the divergence registry**.

## Why the lane's own gates did not see it

This is the interesting part, and it is not carelessness.

The brief told that lane to run `check-dispatchable-frontier.py` before and
after, and it did. That gate reported **only** `F:ml430-nat-squarefree-ext-iff`
moving buckets, which is correct: `classify()` consults the held-out partition
**before** the registry, so a registered divergence affecting a held-out row
changes nothing the frontier can observe.

The gate that does see it is `gen-autogenesis-nursery-refill.py --check`, and
the brief did not name it. **That omission is the coordinator's**, not the
lane's — the lane ran every gate it was given and reported each exit status
honestly.

## The design tension, which is the real finding

`--check` **re-derives an already-drawn family against TODAY's screens.** The
divergence registry only ever grows — every honest divergence found from here
on screens out more rows. So this failure is not a bug in one commit; it is
guaranteed to recur, and any registry entry can trigger it.

Two readings, and they need adjudicating rather than patching:

- **The draw is history.** A family was drawn under the screens in force at the
  time; re-deriving it under later screens asks a question about a tree that no
  longer exists. On this reading `--check` should validate an already-drawn
  family against its **recorded** derivation, not a fresh one, and only fresh
  families face current screens.
- **The floor is a live invariant.** If a drawn family can no longer supply ten
  candidates, the evaluation population it represents has genuinely thinned, and
  that is worth failing over.

The first reading is probably right — ADR-0542 already establishes that repairs
to preregistered populations are **amendment ledgers, never deletions**, and
re-deriving a historical draw under new screens is a silent deletion by another
route. But this should be decided in an ADR with the numbers in front of it,
not settled here.

## What must NOT be done

Do not un-register the five divergences to make the gate green. Each was
verified against Mathlib's source at `c5ea0035…`, and `Squarefree` in
particular is a genuine `Bool`-versus-`Prop` codomain divergence. Removing a
true entry to satisfy a floor would be manufacturing a green gate — the exact
failure this repository measures itself against.

## The rule for briefs

**When a change alters a screen, run every gate that CONSUMES that screen, not
only the gate that reports the thing you changed.** For the divergence
registry that is at least: `check-dispatchable-frontier.py`,
`gen-autogenesis-nursery-refill.py --check`, `check-autogenesis-nursery.py`,
and `check-autogenesis-holdout-isolation.py`. Naming them in the brief is the
whole fix; the lane will run what it is given.
