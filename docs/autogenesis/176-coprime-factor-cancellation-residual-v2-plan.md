# Residual cancellation V2 plan

The exact remaining carrier is the official `Nat.mul_assoc` declaration in the
V1 stream. V2 makes associativity an explicit parameter and threads it through
the multiplicative divisibility witness. No other proof step changes.

The two witness lemmas and residual theorem must compile and reconstruct twice
with empty footprints. The residual theorem then has exactly four parameters:
balanced Bézout, multiplication associativity, right distributivity, and
additive divisibility cancellation.
