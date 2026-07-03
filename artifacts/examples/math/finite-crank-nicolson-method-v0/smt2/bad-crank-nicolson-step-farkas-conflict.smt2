(set-logic QF_LRA)
(declare-const crank_nicolson_next_state Real)

; Exact Crank-Nicolson replay computes the first next state as 3/5.
(assert (= crank_nicolson_next_state (/ 3 5)))

; Malformed resource row claims the first next state is 1/2.
(assert (= crank_nicolson_next_state (/ 1 2)))

(check-sat)
