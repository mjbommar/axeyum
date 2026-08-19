# ADR-0497: Equality elimination infers motive and carrier universes

Status: accepted
Date: 2026-08-19
Index-summary: Construct Eq.rec with motive-first inferred universes and require target-free composition controls before retrying recurrence

## Context

The one-shot `Nat.fib_add_two` operation failed with `expected Prop; got Sort
1`. A target-independent generic transitivity control reproduced the same
failure, proving the recurrence and iterator helper were not required to cause
it. The hand-built eliminators instantiated both `Eq.rec` universes at zero.

The exact imported telescope orders its universe instances as motive then
carrier. A proposition-valued motive over `Nat : Sort 1` therefore requires
`Eq.rec.{0,1}`.

## Decision

Infer the carrier universe from the equality domain, keep the current local
proof motives in `Prop`, and pass `Eq.rec` universe instances in motive-first
order. Pin the order with a negative reversed-order test and require generic
transitivity and congruence to pass with zero axioms and theorem dependencies.

Do not treat these controls as a target execution or proof result. A second
`Nat.fib_add_two` attempt requires a new policy bound to the corrected tooling
and exact control identities.

## Consequences

The measured equality-composition gap is closed without retrying the target.
The constructors now generalize over carrier sorts instead of accidentally
working only for propositions. The next bounded turn can preserve the original
search budget rather than widening it.

