# Lane: first-supplementary-law

Status: **in progress** (opened 2026-08-31)

## Target

The first supplementary law of quadratic reciprocity: for an odd prime
`p = 2m+1`, `-1` is a quadratic residue mod `p` iff `p ≡ 1 (mod 4)`.

## Route being sized

The classical Euler-criterion route needs the CONVERSE of Euler's criterion
(`a^m ≡ 1 → a is a residue`), which `int_prelude/qr_criterion.rs` records as
absent (needs a primitive root or a root-counting argument).

Candidate that AVOIDS the converse: **Wilson's theorem**, which is proved
axiom-free here (`Int.wilson`). `(p-1)! ≡ (-1)^m (m!)^2 [p]`, so at even `m`
(`p ≡ 1 mod 4`) `(m!)^2 ≡ -1 [p]` and `m!` is an explicit residue witness.

Sizing in progress.
