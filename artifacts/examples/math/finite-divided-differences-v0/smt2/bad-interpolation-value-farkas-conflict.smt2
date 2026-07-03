(set-logic QF_LRA)
(declare-const interpolated_value Real)

; Exact replay computes the Newton interpolation value as 10.
(assert (= interpolated_value 10))

; The malformed resource row claims 9.
(assert (= interpolated_value 9))

(check-sat)
