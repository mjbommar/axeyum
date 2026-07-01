; QF_LRA/Farkas obstruction for complex-plane-transforms-v0.
;
; Exact real-pair replay computes conjugate(z*w) = conjugate(z)*conjugate(w)
; = 5 - 5*i for z = 1 + 2*i and w = 3 - i. After shifting both imaginary
; parts by +5, the replayed value is 0 while the malformed claim requires 10.
(set-logic QF_LRA)
(declare-const computed_imaginary_part_plus_five Real)
(declare-const claimed_imaginary_part_plus_five Real)
(assert (= computed_imaginary_part_plus_five 0))
(assert (= claimed_imaginary_part_plus_five 10))
(assert (= computed_imaginary_part_plus_five claimed_imaginary_part_plus_five))
(check-sat)
