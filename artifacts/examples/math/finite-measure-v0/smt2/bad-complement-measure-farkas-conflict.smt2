; QF_LRA complement-measure obstruction for finite-measure-v0.
;
; Exact finite-measure replay computes mu(A) = 1/3 and mu(U) = 1.
; The malformed row claims mu(A^c) = 1/2 while still requiring
; mu(A) + mu(A^c) = mu(U), so the final contradiction is linear.
(set-logic QF_LRA)
(declare-const event_measure Real)
(declare-const complement_measure Real)
(declare-const total_measure Real)
(assert (= event_measure (/ 1 3)))
(assert (= total_measure 1))
(assert (= (+ event_measure complement_measure) total_measure))
(assert (= complement_measure (/ 1 2)))
(check-sat)
