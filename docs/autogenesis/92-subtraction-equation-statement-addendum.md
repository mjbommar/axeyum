# Subtraction-equation statement addendum

Date: 2026-08-20

## Why an addendum is needed

The V2 local proof reached the successor/successor subtraction case before any
kernel submission. Lean 4.30 treats `Nat.sub` as opaque there, so definitional
reduction cannot expose the recursive predecessor subtraction.

Rather than silently introduce a theorem after seeing a compiler diagnostic,
this generated addendum binds exactly one proposition from the immutable
proof-free statement inventory:

```text
Nat.succ_sub_succ_eq_sub :
  forall n m, n.succ - m.succ = n - m
```

## Scope

The statement may be used only to reduce that one branch inside V2's local
`hrestore` proof. It does not authorize another statement name, a source-body
read, theorem-value access, `Nat.sub_add_cancel`, `Nat.add_sub_of_le`, or any
change to the planned proof route.

Its official proof is not presumed empty-footprint. The eventual joint theorem
must still pass the first fresh kernel audit with an empty footprint before a
second reconstruction may run.

## Verification

```sh
python3 scripts/gen-autogenesis-euclidean-subtraction-equation-addendum.py --check
python3 -m unittest \
  scripts.tests.test_gen_autogenesis_euclidean_subtraction_equation_addendum
```
