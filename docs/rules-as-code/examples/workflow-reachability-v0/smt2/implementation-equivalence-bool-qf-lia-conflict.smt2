; Bool/QF_LIA bounded implementation-equivalence check for
; workflow-reachability-v0.
;
; The executable transition predicate and the formal model use the same bounded
; graph transition relation. The fixed representative row below is the
; under_review --approve with supervisor_review--> approved edge. Asking for a
; mismatch on that row is inconsistent.
(set-logic QF_LIA)
(declare-const current_state Int)
(declare-const action Int)
(declare-const next_state Int)
(declare-const supervisor_review Bool)
(declare-const model_allowed Bool)
(declare-const implementation_allowed Bool)

(assert (= current_state 1))
(assert (= action 1))
(assert supervisor_review)
(assert (= next_state 2))
(assert (= model_allowed
  (or
    (and (= current_state 0) (= action 0) (= next_state 1))
    (and (= current_state 1) (= action 1) supervisor_review (= next_state 2))
    (and (= current_state 1) (= action 2) (= next_state 3)))))
(assert (= implementation_allowed
  (or
    (and (= current_state 0) (= action 0) (= next_state 1))
    (and (= current_state 1) (= action 1) supervisor_review (= next_state 2))
    (and (= current_state 1) (= action 2) (= next_state 3)))))
(assert (not (= model_allowed implementation_allowed)))
(check-sat)
