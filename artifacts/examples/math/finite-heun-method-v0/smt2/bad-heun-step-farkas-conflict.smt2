(set-logic QF_LRA)
(declare-const heun_next_state Real)

; Exact Heun replay computes the first next state as 1/4.
(assert (= heun_next_state (/ 1 4)))

; Malformed resource row claims the first next state is 1/2.
(assert (= heun_next_state (/ 1 2)))

(check-sat)
