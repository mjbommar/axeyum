# Lane `int-sumrange`

**Status:** in progress — building `Int.sumRange` and the defining lemmas
Eisenstein's lemma needs (ADR-1260's named obstruction).

The Int prelude folds products only (`Int.prodRange`, 132 rows); no signed
finite sum exists, because Wilson's theorem and Euler's totient theorem both
needed products. Eisenstein's lemma needs subtraction inside a finite sum.

Template: `int_prelude/prod.rs`. References: `Nat.sumRange`, `Rat.sumRange`.
