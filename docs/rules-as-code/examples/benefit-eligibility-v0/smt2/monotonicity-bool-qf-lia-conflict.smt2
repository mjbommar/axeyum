; Bool/QF_LIA monotonicity check for benefit-eligibility-v0.
;
; Source clauses:
; - Rule 1(a): age and residency stay fixed.
; - Rule 1(b): active income threshold is 35000 on/after 2026-07-01.
; - Rule 1(c): sanction status stays false.
; - Rule 1(d): veteran override stays false.
;
; With all exception guards fixed away, increasing income cannot turn an
; ineligible applicant into an eligible one. The bad pattern below requires
; income2 >= income1, income1 above the threshold, and income2 at or below it.
(set-logic QF_LIA)
(declare-const income1 Int)
(declare-const income2 Int)
(declare-const active_threshold Int)
(assert (= active_threshold 35000))
(assert (> income1 active_threshold))
(assert (<= income2 active_threshold))
(assert (>= income2 income1))
(check-sat)
