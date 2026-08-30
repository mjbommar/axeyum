# Lane: int-fib-two-mul — `Int.fib_two_mul` and `Int.fib_two_mul_add_two`

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, int-fib-two-mul, 2026-08-29).** Both targets
landed, kernel-checked and axiom-free, closing `F:ml430-int-fib-two-mul-0e70f3dd`
and `F:ml430-int-fib-two-mul-add-two-0ba4a948`.

- `Int.fib_two_mul : ∀ n, Eq Int (fib (mul two n)) (mul (fib n) (sub (mul two
  (fib (add n one))) (fib n)))`.
- `Int.fib_two_mul_add_two : ∀ n, Eq Int (fib (add (mul two n) two)) (mul
  (fib (add n one)) (add (mul two (fib n)) (fib (add n one))))`.

`int_prelude::` went **46 → 48 passing** (44 → 46 before the two new
concrete-instantiation negative-control tests were added), `derived_laws`
156 → 158 (recounted by grep, not incremented), integer trusted surface
still 0. No induction was needed for either theorem — both are direct
algebra from `Int.fib_add` (already proved) and `Int.fib_rec`.

**The prior lane's sizing was accurate on the algebra and silent on the
actual cost.** "~200–250 lines each, no new device" held for the algebra
itself, and no genuinely new proof DEVICE was needed (everything routes
through `mul_comm`, `left_distrib`, `Int.mul_sub`, `add_assoc`/`add_comm`,
`Int.fib_add`, `Int.fib_rec`). What the sizing didn't — and couldn't —
predict was a mechanical bug that cost most of this lane's time.

## The subtraction bridge

Built first, as the brief asked, before either theorem:

```
/// h : Eq Int (add a b) c  |-  Eq Int b (sub c a)
fn eq_sub_of_add_eq_left(d, a, b, c, h) -> ExprId
```

From `a + b = c` derive `b = c - a`. Route: commute `a+b` to `b+a` (so `h`
reads `b+a = c` after a `trans`), then `Int.add_neg_cancel_right b a :
(b+a)+(-a) = b`; substituting `c` for `b+a` gives `c+(-a) = b` (== `sub c a
= b` after folding `Int.sub`); flip. It is reusable and IS reused —
`fib_pred_eq_sub` (below) is its only consumer so far, but the shape (turn
a recurrence equation into a subtraction) is generic and not tied to
Fibonacci at all.

Detail moved to [`../notes/245-int-fib-two-mul.md`](../notes/245-int-fib-two-mul.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | int-fib-two-mul | `eq_sub_of_add_eq_left`, `fib_pred_eq_sub`: the subtraction bridge (a+b=c \|- b=c-a) and its Fibonacci instance (fib(k-1)=fib(k+1)-fib(k)) |
| 2026-08-29 | int-fib-two-mul | `Int.fib_two_mul` closed (`F:ml430-int-fib-two-mul-0e70f3dd` open → proved), no induction, direct algebra from `Int.fib_add`/`Int.fib_rec` |
| 2026-08-29 | int-fib-two-mul | `Int.fib_two_mul_add_two` closed (`F:ml430-int-fib-two-mul-add-two-0ba4a948` open → proved) |
