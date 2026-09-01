# Lane: constant-canonicity

**Status:** in progress — measuring the constant population before designing anything.

## Question

"Will we end up with ten or twenty definitions of pi?" A type-based duplicate
detector cannot see this: every `CReal`-valued constant has the identical type
`CReal`, so `check-shape-duplicates.py` groups them all or none (measured: none).
`CReal.Equiv` is undecidable, so there is no mechanical test for "same real".

## Landed changes

_(none yet)_
