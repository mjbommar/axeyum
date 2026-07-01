; Bool/QF_LIA terminal-state check for workflow-reachability-v0.
;
; State encoding: submitted=0, under_review=1, approved=2, rejected=3.
; Rule 7(d) makes approved and rejected terminal states. Asking approved to
; move back to under_review contradicts the fixed terminal-state equality.
(set-logic QF_LIA)
(declare-const current_state Int)
(declare-const next_state Int)

(assert (= current_state 2))
(assert (= next_state 1))
(assert (= next_state current_state))
(check-sat)
