; QF_LRA/Farkas obstruction for complex-plane-transforms-v0.
;
; Exact real-pair replay computes i^2 = -1 + 0*i, so the negated real part is
; 1. The malformed row claims the real part of every unit square is positive,
; equivalently that the negated real part is strictly negative.
(set-logic QF_LRA)
(declare-const negated_real_part Real)
(assert (= negated_real_part 1))
(assert (< negated_real_part 0))
(check-sat)
