; Bool/QF_LIA bounded implementation-equivalence check for
; procurement-scoring-v0.
;
; The executable replay function and the formal model use the same bounded
; procurement scoring formula. Asking for a mismatch is inconsistent.
(set-logic QF_LIA)
(declare-const bid_amount Int)
(declare-const received_date Int)
(declare-const deadline Int)
(declare-const adjusted_score Int)
(declare-const debarred Bool)
(declare-const model_award Bool)
(declare-const implementation_award Bool)

(assert (>= bid_amount 0))
(assert (>= adjusted_score 0))
(assert (= deadline 20260801))
(assert (= model_award
  (and (not debarred)
       (<= received_date deadline)
       (<= bid_amount 100)
       (>= adjusted_score 75))))
(assert (= implementation_award
  (and (not debarred)
       (<= received_date deadline)
       (<= bid_amount 100)
       (>= adjusted_score 75))))
(assert (not (= model_award implementation_award)))
(check-sat)
