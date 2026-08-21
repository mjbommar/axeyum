# Official gcd balanced-Bézout exact-reuse plan

The reverse-direction composition stopped before adding any theorem because
`Nat.mod_lt` is already present in the accepted generic balanced-Bézout kernel.
That is a reuse boundary, not a composition failure to weaken or ignore.

The next run is preregistered to compare canonical declaration identities for
`Nat.mod_lt` across the pinned r082 and generic kernels and to require checked
kernel-type-shape compatibility. Only then may it compose the three declarations
that are actually absent: `modLtSucc`, gcd zero-left, and gcd successor.

Two fresh complete invocations must produce byte-identical JSON. Every one of
the six total compositions and six total specializations must independently
replay, and the final official-gcd balanced-Bézout theorem must have an empty
axiom footprint and exactly the frozen direct dependencies. No proof term,
theorem type, or theorem value may be rendered.

The machine-readable authority is
[`official-gcd-balanced-bezout-exact-reuse-plan-v1.json`](../../artifacts/autogenesis/official-gcd-balanced-bezout-exact-reuse-plan-v1.json).
Before accepted execution it grants no theorem, cancellation, Fibonacci,
evaluation, fact, or ledger credit.
