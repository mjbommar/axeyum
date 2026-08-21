# `Int.fib_add_two` residual V1 result and V2 plan

Date: 2026-08-21

The seven-parameter theorem accepts the nonnegative case and all three parity
contracts. Its first compilation stops only because unfolding retains three
negative-constructor matches around the conditional expressions; explicit
`if_pos` and `if_neg` rewrites therefore have no syntactic target.

V2 changes only that presentation: each negative branch is changed directly
to its three conditional natural-Fibonacci expressions before rewriting. The
contracts and proof route are unchanged, no automation is added, and no closed
target submission is authorized.
