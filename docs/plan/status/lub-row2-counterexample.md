# Lane: lub-row2-counterexample

Status: IN PROGRESS (early commit — plan only, nothing built yet)

## Assignment

`docs/curriculum/graded-statement-families.md` §2 records LUB/completeness
(Spivak ch. 8) row 2 — the boundary refutation — as **pure absence**: "the
unavailability is asserted, not proved." Close it, or measure precisely why
it cannot be closed.

## What the two existing row-2 results look like (read, 2026-08-31)

Both are first-order implications taking the CLASSICAL CONCLUSION at a
specific family as a hypothesis and deriving a decision principle:

- `CReal.evt_attained_max_decides_sign : forall v c, le zero c -> le c one ->
  (forall t, le zero t -> le t one -> le (mul t v) (mul c v)) ->
  Or (le v zero) (le zero v)` — `creal/extreme_value.rs`, family
  `CReal.evtLinear v := fun t => mul t v`, plus
  `evtLinear_uniformly_continuous` proving the family is inside EVT's
  hypothesis class.
- `CReal.ivt_exact_root_decides_sign : forall v c, le zero c -> le c one ->
  Equiv (min c (max (add c (neg one)) v)) zero -> Or (le v zero) (le zero v)`
  — `creal/ivt_boundary.rs`, family `CReal.ivtPlateau`, plus its three
  hypothesis-class lemmas.

Both land on **analytic LLPO** (`forall v, v <= 0 or 0 <= v`, i.e. the
`lt_total` `creal/cotransitivity.rs` says is neither assumed nor provable),
and both carry an "Honest scope" section: the classical conclusion is proved
AT LEAST AS STRONG as a decision principle this kernel lacks, not proved
false.

## Planned statement (LUB's own row 2)

Spivak ch. 8's LUB quantifies over an ARBITRARY inhabited bounded-above set,
so the faithful family is a set given by an arbitrary predicate:

```text
CReal.lubSet A := fun x => Or (le x zero) (And A (le x one))
-- i.e. {x <= 0} union ({x <= 1} if A)
```

inhabited at `zero`, bounded above by `one`. Given a supremum `s` with the
upper-bound law and the APPROXIMATION law (`forall t < s, exists x in S,
t < x` — the "least" half in the form the constructive reals need),
`lt_cotrans` on `zero_lt_one` at `z := s` gives `0 < s or s < 1`, and each
branch decides `A`:

- `0 < s` -> approximation at `t := 0` -> some `x` in `S` with `0 < x` -> the
  `x <= 0` disjunct is absurd -> `A`.
- `s < 1` -> if `A` then `1` is in `S` so `1 <= s`, contradiction -> `Not A`.

Conclusion `Or A (Not A)` for an ARBITRARY `A : Prop` — **unrestricted
excluded middle**, which ADR-0716 §2 measures as absent from this kernel
(only `Decidable.em`, which takes a `Decidable` instance). That is a
STRICTLY STRONGER boundary than IVT's/EVT's LLPO.

## Next

Build it in a new `crates/axeyum-lean-kernel/src/creal/lub_boundary.rs`.
