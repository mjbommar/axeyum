; QF_UF value conflict for finite-simplicial-cohomology-v0.
;
; Finite replay computes delta f([a,c]) = 0 over F2. The malformed row claims
; the same coboundary value is 1.
(set-logic QF_UF)
(declare-sort Bit 0)
(declare-fun zero () Bit)
(declare-fun one () Bit)
(declare-fun delta_ac () Bit)
(assert (= delta_ac zero))
(assert (= delta_ac one))
(assert (not (= zero one)))
(check-sat)
