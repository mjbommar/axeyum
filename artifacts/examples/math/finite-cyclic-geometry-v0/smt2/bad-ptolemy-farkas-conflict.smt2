; QF_LRA Ptolemy obstruction for finite-cyclic-geometry-v0.
;
; Finite replay computes Ptolemy's two sides for the 4-by-3 cyclic rectangle:
; AC*BD = 25 and AB*CD + BC*DA = 16 + 9 = 25. This artifact checks the
; malformed claim that the same replayed right-hand side is 24 after replay
; has reduced the row to exact rational linear arithmetic.
(set-logic QF_LRA)
(declare-const ptolemy_rhs Real)
(assert (= ptolemy_rhs 25))
(assert (= ptolemy_rhs 24))
(check-sat)
