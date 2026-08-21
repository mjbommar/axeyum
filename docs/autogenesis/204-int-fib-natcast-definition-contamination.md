# `Int.fib_natCast` definition contamination

Date: 2026-08-21

The corrected rooted execution compiled and exported the direct `rfl` theorem.
Two independent imports produced byte-identical observations and zero direct
theorem dependencies. Nevertheless, the theorem retains the complete nine-name
assumption footprint carried by the official integer Fibonacci environment.

This is stronger localization than a failed proof: proof search is not the
problem. Even reflexivity over official `Int.fib` inherits representation or
definition contamination. The exact fact receives no credit. The next step is
a non-rendering declaration/definition closure audit for `Int.fib`, followed by
a target-owned clean representation reconstruction rather than another theorem
proof attempt.
