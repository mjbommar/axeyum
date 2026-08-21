# Clean `Int.fib_add_two` construction plan

Date: 2026-08-21

Admission of exact `Int.fib_natCast` made this fact newly ready. The official
integer recurrence cannot be reused: its proof cycles through
`Int.fib_neg_natCast` and carries the same parity-instance assumptions that the
target-owned representation removed.

The first direct construction therefore splits the two integer constructors
and explicit natural parity cases over the target-owned definition. It may use
only the admitted natural-cast bridge, the clean natural Fibonacci recurrence,
and explicit arithmetic transport. One compile and one target submission are
allowed. If compilation fails, the diagnostics are retained and there is no
same-plan retry, export, import, or theorem credit.
