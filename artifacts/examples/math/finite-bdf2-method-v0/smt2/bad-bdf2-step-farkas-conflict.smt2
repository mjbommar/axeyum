(set-logic QF_LRA)
(declare-const bdf2_next_state Real)

; Exact replay computes the first BDF2 multistep next state as 5/12.
(assert (= bdf2_next_state (/ 5 12)))

; The malformed source row claims the same next state is 1/3.
(assert (= bdf2_next_state (/ 1 3)))

(check-sat)
