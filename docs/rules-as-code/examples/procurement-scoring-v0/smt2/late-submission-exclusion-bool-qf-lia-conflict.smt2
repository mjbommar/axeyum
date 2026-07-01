; Bool/QF_LIA late-submission check for procurement-scoring-v0.
;
; Source clauses:
; - Rule 4(d): a timely bid is received on or before the deadline.
; - Rule 4(f): award includes the timeliness guard.
;
; Dates are encoded as YYYYMMDD integers for this compact regression.
(set-logic QF_LIA)
(declare-const received_date Int)
(declare-const deadline Int)
(declare-const on_time Bool)
(declare-const debarred Bool)
(declare-const within_bid_cap Bool)
(declare-const adjusted_score Int)
(declare-const award Bool)

(assert (= received_date 20260802))
(assert (= deadline 20260801))
(assert (= on_time (<= received_date deadline)))
(assert (not debarred))
(assert within_bid_cap)
(assert (>= adjusted_score 75))
(assert (= award (and (not debarred) on_time within_bid_cap (>= adjusted_score 75))))
(assert award)
(check-sat)
