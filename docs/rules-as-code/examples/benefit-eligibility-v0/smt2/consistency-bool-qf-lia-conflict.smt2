; Bool/QF_LIA consistency check for benefit-eligibility-v0.
;
; Source clauses:
; - Rule 1(a): adult resident base requirement.
; - Rule 1(b): active income threshold.
; - Rule 1(c): sanctioned applicants are ineligible.
;
; For the fixed adult resident, unsanctioned, at-threshold applicant below,
; the rule model defines `ineligible` as the negation of `eligible`. Asking
; for both outputs at once is therefore inconsistent.
(set-logic QF_LIA)
(declare-const age Int)
(declare-const income Int)
(declare-const standard_threshold Int)
(declare-const resident Bool)
(declare-const sanctioned Bool)
(declare-const eligible Bool)
(declare-const ineligible Bool)
(assert (= age 18))
(assert (= income 35000))
(assert (= standard_threshold 35000))
(assert resident)
(assert (not sanctioned))
(assert (= eligible (and resident (>= age 18) (not sanctioned) (<= income standard_threshold))))
(assert (= ineligible (not eligible)))
(assert eligible)
(assert ineligible)
(check-sat)
