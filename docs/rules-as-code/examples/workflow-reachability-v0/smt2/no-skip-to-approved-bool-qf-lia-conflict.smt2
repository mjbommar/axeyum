; Bool/QF_LIA no-skip check for workflow-reachability-v0.
;
; State encoding: submitted=0, under_review=1, approved=2, rejected=3.
; Action encoding: request_review=0, approve=1, reject=2.
;
; The fixed request below asks an application in submitted to approve directly.
; The transition relation has no submitted -> approved edge.
(set-logic QF_LIA)
(declare-const current_state Int)
(declare-const action Int)
(declare-const next_state Int)
(declare-const supervisor_review Bool)
(declare-const transition_allowed Bool)

(assert (= current_state 0))
(assert (= action 1))
(assert (= next_state 2))
(assert (= transition_allowed
  (or
    (and (= current_state 0) (= action 0) (= next_state 1))
    (and (= current_state 1) (= action 1) supervisor_review (= next_state 2))
    (and (= current_state 1) (= action 2) (= next_state 3)))))
(assert transition_allowed)
(check-sat)
