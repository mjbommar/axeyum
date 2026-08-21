# Integer Fibonacci support audit failure

Date: 2026-08-21

The preregistered two-root importer invocation returned no completed audit
document from the sealed `Int.fib_neg` closure. The zero-byte stdout and single
read are archived; no retry occurred. Because child stderr was not retained,
the result intentionally does not claim which root was absent.

Neither support received credit. A fresh root-selected export is required,
starting with the dependency-free open fact `Int.fib_natCast`, before the
negative-index recurrence may use either support.
