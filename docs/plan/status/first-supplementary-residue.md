# Lane: first-supplementary-residue

Status: IN PROGRESS (early commit — orientation only)

## Target

`p ≡ 1 (mod 4) ⟹ −1 IS a quadratic residue mod p` — the residue half of the
first supplementary law. ADR-1230 landed the non-residue half and named the
route: Wilson's theorem gives `(p−1)! = (−1)^m (m!)^2`, so at even `m` the
witness is `m!` outright, with no converse of Euler's criterion.

## Landed

(nothing yet)

## Notes

- ADR number reserved: 1235.
