; QF_LRA/Farkas obstruction for orientation-area-geometry-v0.
;
; Exact affine-area replay computes image signed double area 60 for a source
; signed double area 12 under determinant 5. This artifact checks the malformed
; claim that the affine map preserves signed double area.
(set-logic QF_LRA)
(declare-const source_signed_double_area Real)
(declare-const image_signed_double_area Real)
(declare-const scaled_signed_double_area Real)
(assert (= source_signed_double_area 12))
(assert (= scaled_signed_double_area 60))
(assert (= image_signed_double_area scaled_signed_double_area))
(assert (= image_signed_double_area source_signed_double_area))
(check-sat)
