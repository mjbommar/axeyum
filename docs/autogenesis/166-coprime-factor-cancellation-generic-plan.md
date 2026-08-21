# Generic coprime-factor cancellation plan

Official-representation balanced Bézout is now closed. The next proof is kept
generic over that one certificate theorem so its algebra can be reconstructed
and audited independently before any official-kernel specialization.

The intended statement says that if `gcd a c = 1`, `d ∣ a`, and
`d ∣ c*b`, then `d ∣ b`. Its proof multiplies a balanced-natural Bézout
certificate by `b`, shows every term except the leading `b` is divisible by
`d`, and cancels the divisible tail. It uses no subtraction, proof search, or
upstream proof body.

One source compilation and one root-selected export are allowed on the pinned
Lean 4.30 `s5` environment. Two fresh imports must agree byte-for-byte and have
an empty footprint. This increment grants no official specialization or
Fibonacci authority.

The machine-readable boundary is
[`coprime-factor-cancellation-generic-plan-v1.json`](../../artifacts/autogenesis/coprime-factor-cancellation-generic-plan-v1.json).
