; Bool/QF_LIA bid-cap check for procurement-scoring-v0.
;
; Source clauses:
; - Rule 4(b): awardable bids must be at most 100 units.
; - Rule 4(f): award includes the bid-cap guard.
;
; The fixed request is timely, not debarred, and has enough score, but its bid
; exceeds the cap. Asking for award is inconsistent.
(set-logic QF_LIA)
(declare-const bid_amount Int)
(declare-const max_bid Int)
(declare-const within_bid_cap Bool)
(declare-const debarred Bool)
(declare-const on_time Bool)
(declare-const adjusted_score Int)
(declare-const award Bool)

(assert (= bid_amount 101))
(assert (= max_bid 100))
(assert (= within_bid_cap (<= bid_amount max_bid)))
(assert (not debarred))
(assert on_time)
(assert (>= adjusted_score 75))
(assert (= award (and (not debarred) on_time within_bid_cap (>= adjusted_score 75))))
(assert award)
(check-sat)
