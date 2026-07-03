(set-logic QF_LRA)
(declare-const rk_next_state Real)

; Exact RK2 midpoint replay computes the first next state as 1/4.
(assert (= rk_next_state (/ 1 4)))

; Malformed resource row claims the first next state is 1/2.
(assert (= rk_next_state (/ 1 2)))

(check-sat)
