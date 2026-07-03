(set-logic QF_LRA)
(declare-const adams_bashforth_next_state Real)

; Exact Adams-Bashforth replay computes the first multistep next state as 1.
(assert (= adams_bashforth_next_state 1))

; Malformed resource row claims the first multistep next state is 3/4.
(assert (= adams_bashforth_next_state (/ 3 4)))

(check-sat)
