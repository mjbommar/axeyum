# Corrected Fibonacci recurrence v2 selection

Date: 2026-08-19

## Decision

Preregister one corrected `Nat.fib_add_two` execution under
`nat-fib-iterate-recurrence-v2`. The target and search ceiling do not change:

- one iterator-successor helper schema;
- two ordered templates: direct normalization, then recurrence composition;
- at most two kernel submissions;
- one executor invocation; and
- zero retries.

The executable is pinned at `1880e56db`. Before execution, its synthetic
universe-order and transitivity tests plus the exact imported composition
control must reproduce the three hashes recorded in the v2 policy.

## Why a second execution is justified

The v1 result localized an exact constructor error. The repair did not inspect
a Mathlib proof body, held-out data, or a successful historical target outcome.
It changed no search template and widened no budget. Target-independent tests
now reject the old and reversed universe orders while admitting the corrected
generic terms.

That makes v2 a controlled repair evaluation, not an unbounded retry. The v1
negative result remains immutable and independently useful even if v2 fails.

## Credit boundary

This policy performs no target execution and grants no credit. A v2 candidate,
if accepted, still requires a semantic theorem receipt and a separate ordinary
fact admission before `Nat.fib_add_two` can change state or unlock its child.

