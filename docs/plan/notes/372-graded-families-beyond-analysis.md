# Notes: 372-graded-families-beyond-analysis

Detail moved out of [`../status/372-graded-families-beyond-analysis.md`](../status/372-graded-families-beyond-analysis.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

- **Number theory.** Seven families proposed. Row 1 is unusually strong and
  mostly landed (infinitude of primes, Fermat, totient multiplicativity,
  Wilson both directions, UFD existence). Row 2 is empty in the analysis sense
  for all of them, argued from shape per Amendment 3. The subject's **one**
  genuine row 2 is the least-number principle, unbuilt. Row 3 — which ADR-0716
  moves the dominance argument onto — **barely exists**: `is_prime`,
  `factorize`, `crt`, `legendre_symbol` are bare computation with no verifier
  (control: 19 `verify_*`/`check_*` functions exist in the same crate, none
  number-theoretic). The one real exception is
  `prove_lia_unsat_by_diophantine_certified`/`check_diophantine_certificate`.
- **Linear algebra.** The type-theory premise was refuted by measurement:
  `Rat.dotN_cauchy_schwarz` proves general-dimension Cauchy–Schwarz over ℚ at 0
  axioms, on the same finite-function encoding number theory uses. The real
  bound is that `funext` is absent (control: `congrFun'`, FOUND), so matrix
  identities must be stated **pointwise**. `Rat.sumRange_swap` makes the matrix
  layer assembly rather than new mathematics.

## Highest-yield next targets

1. `Nat.lnp_unrestricted_implies_em` — number theory's only row 2, and a
   stronger boundary than any analysis one. Coordinate: four sibling lanes are
   in `nat_prelude/`.
2. Euler's theorem `a^φ(n) ≡ 1 (mod n)` — both residue-permutation ingredients
   (`Int.euler_unit_coprime`, `Int.euler_unit_injective`) already landed.
3. The matrix layer over `Nat → Nat → Rat` — unlocks three LA families' row 1
   at once; state everything pointwise.

## Left open, deliberately

`curriculum.toml`'s `covered` conflates "a decidable exercise exists" with "a
general kernel theorem exists", which is why `number-theory` and
`linear-algebra` read identically in the map while their kernel content differs
sharply. Splitting that status is a schema change with a validator and an
`axeyum-scenarios::mathtour` mirror behind it, and belongs in its own ADR.

## Checks run

- `scripts/cargo-serialized.sh build --release …` (fresh binaries — the
  stale-prebuilt trap invalidates ABSENT verdicts, and this lane turns on
  several): clean, 47.3 s.
- `shape_search --include-constructed`: 2,426 declarations indexed.
- `python3 scripts/gen-adr-index.py --check`: exit 0, `rows=630`.
- `./scripts/check-links.sh`: `all links ok`.
- No `cargo test` run — this lane changed no Rust.
