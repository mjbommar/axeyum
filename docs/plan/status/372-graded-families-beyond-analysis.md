# Lane 372 — graded statement families beyond analysis

<!-- plan-section: lane-status -->

Status: **COMPLETE** (2026-08-30) — design/measurement lane, no kernel
declarations built, no fact edited.

Extended ADR-0603's graded-statement-family treatment from the four Spivak
real-analysis families (MVT, LUB, Taylor remainder, FTA) to **number theory**
(Stein, Shoup) and **linear algebra** (Boyd–Vandenberghe), the curriculum's two
untreated destinations.

## The central finding

`Nat.le_total`, `Int.le_total`, `Rat.le_total` and `Rat.le_or_lt` are **proved,
axiom-free theorems**, while `CReal.le_total`/`lt_total` are absent (controls:
`CReal.lt_cotrans`, `CReal.apart_cotrans`, FOUND). So the decision principle
that every real-analysis row 2 extracts is *already in the environment* for
ℕ/ℤ/ℚ, and no number-theoretic or rational-linear-algebra statement can have a
row 2 of that kind. That is a positive measurement of emptiness, not a failure
to find one — the distinction ADR-0603 Amendment 4 exists to protect.

Two boundaries survive, and one is **stronger** than anything analysis
produces: the unrestricted least-number principle reduces to *full* excluded
middle (analysis's row 2s reach only LLPO). The other is not a decision
boundary at all but an expressiveness one, and gets its own row.

## Landed

| Change | Path |
|---|---|
| The measurement note: families, rows, targets, both subjects | `docs/curriculum/graded-statement-families-number-theory-and-linear-algebra.md` |
| ADR: row 2 of a decidable subject; introduces **row 2′** | `docs/research/09-decisions/adr-0716-row-two-of-a-decidable-subject.md` |
| Corrected — 3 of 4 "Lean-horizon" theorems are landed | `docs/curriculum/03-destinations/number-theory.md` |
| Corrected — the kernel layer was missing entirely | `docs/curriculum/03-destinations/linear-algebra.md` |
| Lens note: the ✅/◐/✗ tags measure row 3 only | `docs/curriculum/foundational-books/source-tocs.md` |
| Comparison table now separates scenario from kernel layer | `docs/curriculum/DEPTH.md` |

`curriculum.toml` was deliberately **not** touched — see "left open" below.

## Verdicts

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
