# Clean `Int.fib_add_two` V3 plan

Date: 2026-08-21

V3 replaces the remaining broad conditional simplification with three named
mod-two equalities: the current negative index, its successor, and its second
successor. The two standard successor-parity equivalences derive them in each
of the zero/one cases. Only after those identities exist does the proof unfold
the target-owned Fibonacci definition and apply the natural recurrence.

The representation, premises, and no-search boundary remain unchanged. One
compile is authorized; failure receives no same-plan retry or theorem credit.
