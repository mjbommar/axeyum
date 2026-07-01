; QF_LRA/Farkas obstruction for least-squares-regression-v0.
;
; Exact replay computes baseline_rss - model_rss = 14/3 - 1/6 = 9/2. The
; malformed row claims the improvement is 4.
(set-logic QF_LRA)
(declare-const rss_improvement Real)
(assert (= rss_improvement (/ 9 2)))
(assert (= rss_improvement 4))
(check-sat)
