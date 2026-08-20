# ADR-0557: Bound Hayes power-sum history by conductor width

Status: accepted
Date: 2026-08-20
Index-summary: Replace all-degree Hayes power-sum history and tree unit lookup by an exact conductor-width circular recurrence and dense index

## Context

The modular Hayes population engine computes the logarithmic derivative

```text
Lambda_n(chi)=n A_n(chi)-sum_(1<=j<n) Lambda_j(chi) A_(n-j)(chi).
```

It previously retained `Lambda_0,...,Lambda_n` as separate vectors of length
`2^ell`.  At the Lemire endpoints `n=2ell+1,2ell+2`, this kept roughly twice
as much power-sum history as the recurrence can read.  The same route also
represented the bijection from packed principal units to mixed-radix indices
as a `BTreeMap`, although the packed odd units already form the dense domain
`0,...,2^ell-1` after shifting away their constant bit.

## Decision

Use the conductor identity

```text
A_d(chi)=0 for every nontrivial chi and d>=ell.
```

For such a character, `Lambda_n(chi)` therefore depends only on
`Lambda_(n-1)(chi),...,Lambda_(n-ell+1)(chi)`.  Retain exactly `ell` rows in a
circular table.  The overwritten row is `ell` steps old, whose multiplier is
`A_ell(chi)=0`, so it is no longer a dependency.  After the group transforms,
the recurrence for each character is independent.  Evaluate deterministic
blocks of `2^15` nontrivial characters and copy only each target value into the
full output vector; the circular history is therefore `ell*min(2^15,2^ell-1)`
cells rather than `ell*2^ell`.  Handle the trivial character separately by its
exact closed form

```text
A(z)=1/(1-2z),  Lambda_n=2^n.
```

Replace the local unit `BTreeMap` by a dense vector indexed by `unit>>1`.
Initialization rejects duplicate or missing coordinates before any transform;
all subsequent lookups are bounds-checked dense indices.

## Evidence

- Exact identity-class irreducible counts through degree 20 remain unchanged,
  including composite degrees and proper prime powers.
- The new one-prime odd endpoint agrees field-for-field with the independent
  two-prime transform plus full classwise inversion through `ell=12`.
- Existing endpoint, distribution, conductor, Möbius, and extension-trace
  operations share the same power-sum routine, so the full crate gate remains
  the release condition.
- The circular dependency excludes the row exactly `ell` steps old; a mutation
  that includes it would multiply by a nonexistent nontrivial `A_ell` term and
  is caught by the two-prime comparison.
- The focused `gf2_hayes` library suite passes `109` tests with zero failures
  and five explicitly ignored extended probes; all-target, all-feature
  `axeyum-cas` Clippy also passes with warnings denied.
- The first character-block boundary is exercised at `ell=16`; it reproduces
  the independently retained exact row `N_33(1)=133816`, `I_33(1)=4055`.
- On the same `s5` host and exact `(ell,n)=(22,45)` input, the full-width v2
  recurrence and blocked v3 recurrence both return
  `N_45(1)=8381026`, `I_45(1)=186245`.  Blocking reduces peak RSS from
  `1,476,932` to `794,376` KiB and wall time from `88.177` to `78.292`
  seconds.  The v3 binary SHA-256 is
  `2218173d6356b812acc3a7c17c8706e9e3ae910618b15e0919467f65845ede42`;
  its complete timing log SHA-256 is
  `d8812cd747fee2051da0cbe7f9a0d9a407e74632da8093e4e0274081a993fb3f`.

## Alternatives

- **Retain all rows for simplicity:** rejected.  It makes high-level exact
  controls consume memory for values that are mathematically unreachable from
  the target recurrence.
- **Apply the circular recurrence to the trivial character:** rejected.  Its
  coefficients do not vanish above the conductor; the closed form is both
  simpler and exact.
- **Use an unchecked packed-unit permutation:** rejected.  Duplicate and
  completeness checks remain mandatory before dense lookup.

## Consequences

- The dominant modular recurrence retains `ell` block-width rows rather than
  `n+1` full-character vectors and scans at most `ell-1` prior degrees per
  target row.
- The transformed class-sum rows remain one conductor width, while recurrence
  history is bounded independently of the full character population.  At
  large levels this removes almost the entire second conductor-width matrix,
  excluding the one target vector, fixed maps, and transform scratch space.
- This is an exact CAS improvement, not a new cancellation estimate.  It makes
  larger stopping tests cheaper but gives no universal Lemire theorem credit.
