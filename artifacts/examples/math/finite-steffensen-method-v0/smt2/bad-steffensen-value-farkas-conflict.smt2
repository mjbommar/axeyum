(set-logic QF_LRA)
; Source-linked scalar conflict for finite-steffensen-method-v0.
; Exact replay computes steffensen_value = 1 for g(x)=(x+1)/2 from x0=0,
; while the malformed row claims steffensen_value = 3/2.
(declare-const steffensen_value Real)
(assert (= steffensen_value 1))
(assert (= steffensen_value (/ 3 2)))
(check-sat)
