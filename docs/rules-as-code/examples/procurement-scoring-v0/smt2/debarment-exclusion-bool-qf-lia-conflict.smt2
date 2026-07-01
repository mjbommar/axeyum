; Bool/QF_LIA debarment-exclusion check for procurement-scoring-v0.
;
; Source clauses:
; - Rule 4(c): a debarred vendor is not awardable.
; - Rule 4(f): award includes the guard (not debarred).
;
; The fixed request is otherwise awardable, but the vendor is debarred.
; Asking for award is inconsistent.
(set-logic QF_LIA)
(declare-const debarred Bool)
(declare-const on_time Bool)
(declare-const within_bid_cap Bool)
(declare-const adjusted_score Int)
(declare-const award Bool)

(assert debarred)
(assert on_time)
(assert within_bid_cap)
(assert (>= adjusted_score 75))
(assert (= award (and (not debarred) on_time within_bid_cap (>= adjusted_score 75))))
(assert award)
(check-sat)
