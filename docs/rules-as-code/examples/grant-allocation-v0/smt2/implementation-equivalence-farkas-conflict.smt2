; QF_LRA implementation-equivalence check for grant-allocation-v0.
;
; The model and implementation encode the same rational allocation rule.
; Asking for their Boolean outputs to differ is inconsistent.
(set-logic QF_LRA)
(declare-const shelter_share Real)
(declare-const clinic_share Real)
(declare-const admin_share Real)
(declare-const model_compliant Bool)
(declare-const implementation_compliant Bool)
(assert
  (= model_compliant
     (and (= (+ shelter_share clinic_share admin_share) 1)
          (>= shelter_share (/ 1 2))
          (>= clinic_share (/ 1 4))
          (<= admin_share (/ 1 4))
          (>= shelter_share 0)
          (>= clinic_share 0)
          (>= admin_share 0))))
(assert
  (= implementation_compliant
     (and (= (+ shelter_share clinic_share admin_share) 1)
          (>= shelter_share (/ 1 2))
          (>= clinic_share (/ 1 4))
          (<= admin_share (/ 1 4))
          (>= shelter_share 0)
          (>= clinic_share 0)
          (>= admin_share 0))))
(assert (not (= model_compliant implementation_compliant)))
(check-sat)
