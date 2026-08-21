# ADR-0588: Price translation zeros at exact conductor

Status: accepted
Date: 2026-08-21
Index-summary: Separate cumulative translation-fixed characters from the exact-conductor zeros they force

## Context

ADR-0587 proves that the translation-fixed dual through level `ell` has order
`2^ceil(ell/2)`.  At odd polynomial degree, exactly half of that cumulative
dual has negative translation sign and its Mangoldt and squared-discrepancy
Fourier coefficients vanish.  That cumulative statement does not itself say
how many zeros occur among characters of *exact* conductor.  Confusing the
two populations overstates the primitive odd-level saving by a factor of two.

## Decision

Extend `hayes_translation_spectral_involution` with one typed row for every
exact character level `j`.  Write

```text
F_j = 2^ceil(j/2),   F_0=1,
```

for the number of translation-fixed characters through level `j`.  Restriction
commutes with translation, so the number fixed at exact level is

```text
f_j = F_j-F_(j-1)
    = 1                         if j=1,
      0                         if j is even,
      2^((j-1)/2)              if j>=3 is odd.                 (FIX)
```

If the polynomial degree `n` is even, ADR-0587 puts the translation class in
the commutator image and no fixed character has negative sign.  If `n` is
odd, the negative cumulative population is `Z_j=F_j/2` for `j>=1`, with
`Z_0=0`.  Therefore the forced zeros of exact level are

```text
z_j = Z_j-Z_(j-1)
    = 1                         if j=1,
      0                         if j is even,
      2^((j-3)/2)              if j>=3 is odd.                 (ZERO)
```

The CAS derives character conductors from the 2-typical Witt coordinates,
tests fixedness by evaluating every admitted character on the commutators of
all canonical generators, tests the translation sign exactly, and rejects any
disagreement with `(FIX)` or `(ZERO)`.  It also requires the exact rows to
recover the full cumulative counts.

## Evidence

- `translation_spectral_involution_checks_the_complete_character_group`
  exhausts both Lemire endpoint parities for `2<=ell<=8`.
- At `ell=8`, the odd-degree `(fixed,zero)` rows are
  `(1,1),(0,0),(2,1),(0,0),(4,2),(0,0),(8,4),(0,0)`; their eight zeros recover
  the cumulative count.
- The same exact fixed rows occur at even polynomial degree, but every zero
  count is zero.
- Focused tests and all-feature CAS `lib`/`bins`/`tests` Clippy pass.  Examples
  are excluded because the worktree contains protected untracked reviewer
  experiments with unrelated pre-existing Clippy findings.

## Consequences

- At odd `j>=3`, the forced-zero fraction among all `2^(j-1)` exact-level
  characters is only `2^(-(j+1)/2)`.  It tends to zero exponentially.
- The translation involution provides exact reusable cancellation, but neither
  a constant-density odd saving nor any even-endpoint saving.  It therefore
  does not prove `(WITT-LOW)`, `(REL)`, or Lemire's conjecture.
- Any second-symmetry argument must act nontrivially on the residual primitive
  characters rather than count ADR-0587's cumulative fixed dual again.
