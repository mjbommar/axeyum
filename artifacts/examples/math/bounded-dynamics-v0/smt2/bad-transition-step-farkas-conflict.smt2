; QF_LRA/Farkas obstruction for bounded-dynamics-v0.
;
; Exact replay computes 2 + 2 = 4 for the next state.
; This artifact checks the malformed claim that the same next state is 5.
(set-logic QF_LRA)
(declare-const previous_state Real)
(declare-const delta Real)
(declare-const next_state Real)
(assert (= previous_state 2))
(assert (= delta 2))
(assert (= next_state (+ previous_state delta)))
(assert (= next_state 5))
(check-sat)
