; QF_LRA total-budget check for grant-allocation-v0.
;
; The source rule requires the three allocation shares to sum to exactly 1.
; Asking for the same total to be 5/4 is inconsistent.
(set-logic QF_LRA)
(declare-const shelter_share Real)
(declare-const clinic_share Real)
(declare-const admin_share Real)
(declare-const total_share Real)
(assert (= total_share (+ shelter_share clinic_share admin_share)))
(assert (= total_share 1))
(assert (= total_share (/ 5 4)))
(check-sat)
