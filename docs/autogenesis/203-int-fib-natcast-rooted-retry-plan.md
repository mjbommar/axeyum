# Rooted `Int.fib_natCast` construction retry

Date: 2026-08-21

The direct `rfl` theorem compiled, but the first exporter invocation could not
find a module artifact because plain `lean` did not place an olean in Mathlib's
build-library search path. No theorem was submitted or credited.

V2 preserves the exact proof and changes only artifact placement: one compile
writes the olean explicitly under `.lake/build/lib/lean`, followed by one export
and two imports. Both temporary paths are removed afterward. This is a new
preregistered execution, not a hidden retry of V1.
