; QF_LRA/Farkas obstruction for bounded-dynamics-v0.
;
; Exact replay computes state_at_claimed_step = 6 for step 2, below threshold 7.
; This artifact checks the malformed claim that step 2 already reaches the threshold.
(set-logic QF_LRA)
(declare-const state_at_claimed_step Real)
(declare-const threshold Real)
(assert (= state_at_claimed_step 6))
(assert (= threshold 7))
(assert (>= state_at_claimed_step threshold))
(check-sat)
