; Bool/QF_LIA score-monotonicity check for procurement-scoring-v0.
;
; Source clauses:
; - Rule 4(a): award threshold is applied to adjusted score.
; - Rule 4(e): the same small-business bonus is added to both compared bids.
;
; With all non-score guards fixed, a higher quality score cannot lose an award
; that a lower quality score received.
(set-logic QF_LIA)
(declare-const quality1 Int)
(declare-const quality2 Int)
(declare-const bonus Int)
(declare-const award1 Bool)
(declare-const award2 Bool)

(assert (>= quality1 0))
(assert (<= quality1 100))
(assert (>= quality2 0))
(assert (<= quality2 100))
(assert (>= quality2 quality1))
(assert (or (= bonus 0) (= bonus 5)))
(assert (= award1 (>= (+ quality1 bonus) 75)))
(assert (= award2 (>= (+ quality2 bonus) 75)))

(assert award1)
(assert (not award2))
(check-sat)
