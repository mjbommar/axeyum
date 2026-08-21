# Multiplicative witness carrier is exact

The same-stream audit resolves the apparent contradiction. `Eq.trans` and
`congrArg` are empty-footprint, while this stream's exact `Nat.mul_assoc`
declaration reaches `propext` directly and has no theorem dependencies.

The residual theorem should therefore receive associativity as an explicit
parameter and later specialize it with the already accepted target-owned clean
leaf. No multiplicative witness or cancellation credit is granted yet.

The sealed manifest SHA-256 is
`ec3957b48ceb2e00af8dde6a9272ab3f5e887acd4a1e257934e4d103365ede55`.
