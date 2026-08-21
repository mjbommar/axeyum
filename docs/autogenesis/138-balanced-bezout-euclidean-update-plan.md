# Explicit balanced-Bézout Euclidean update plan

Date: 2026-08-21

The pointwise quotient witness is now accepted, but it is not yet composed into
gcd induction. This increment isolates the other missing piece: the arithmetic
transformation that turns a balanced Bézout certificate for `(r, d)` into one
for `(d, n)` when `d*q + r = n`.

The four-Nat witness map is the same one already constructed by the native
kernel prelude:

```text
new_mp = np + q*mn
new_mn = nn + q*mp
new_np = mp
new_nn = mn
```

The source translates the native constructor's equality chain explicitly. It
uses pointwise `congrArg`, Nat distributivity and associativity, and adjacent
sum permutations. It contains no `rw`, `simp`, `ring`, public quotient,
function equality, or rewriting under a binder.

One compilation, one export, and at most two fresh importer runs are authorized
on pinned `s5`. Acceptance requires byte-identical empty-footprint audits and
no forbidden dependency. Compilation failure or a nonempty first audit ends
V1 without retry. The exact three-file pre-existing baseline must survive, and
the source plus its two generated outputs are the entire cleanup scope.

Even on success this result grants only the arithmetic update. Composition
with the quotient witness and official `Nat.gcd.induction` is a later,
separately preregistered theorem submission.

```sh
python3 scripts/check-autogenesis-balanced-bezout-euclidean-update-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_balanced_bezout_euclidean_update_plan
```
