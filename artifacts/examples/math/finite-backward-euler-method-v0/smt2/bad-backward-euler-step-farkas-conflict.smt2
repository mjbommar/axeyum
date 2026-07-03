(set-logic QF_LRA)
(declare-const backward_euler_next_state Real)

; Exact backward Euler replay computes the first next state as 2/3.
(assert (= backward_euler_next_state (/ 2 3)))

; Malformed resource row claims the first next state is 1/2.
(assert (= backward_euler_next_state (/ 1 2)))

(check-sat)
