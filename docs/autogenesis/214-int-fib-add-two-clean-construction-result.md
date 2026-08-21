# First clean `Int.fib_add_two` construction result

Date: 2026-08-21

The first source closed the nonnegative case and the two boundary values
`-1` and `-2`. Its single compiler invocation stopped with two symbolic
negative-successor goals. Natural parity was already split correctly, but
Lean retained constructor-level expressions for adding one and two to a
negative integer and did not normalize the resulting alternating-sign sum.

No export, importer run, target submission, search invocation, or ledger write
occurred. The temporary source and olean paths were removed and the exact
three-file `s5` baseline was restored. The next construction must supply
explicit negative-successor addition equations and a sign-normalized form of
the natural Fibonacci recurrence rather than asking broad simplification to
discover both transformations.
