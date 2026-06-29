; QF_UF scalar-closure conflict for finite-modules-v0.
;
; The malformed subset has 1 present but 2 absent, while the Z/4Z regular
; module table gives 2 * 1 = 2. Scalar closure would require 2 * 1 to remain
; present, so the row is refuted by EUF over the fixed table facts.
(set-logic QF_UF)
(declare-sort R 0)
(declare-sort M 0)
(declare-sort Membership 0)
(declare-fun present () Membership)
(declare-fun absent () Membership)
(declare-fun r2 () R)
(declare-fun m1 () M)
(declare-fun m2 () M)
(declare-fun smul (R M) M)
(declare-fun in_subset (M) Membership)
(assert (not (= present absent)))
(assert (= (in_subset m1) present))
(assert (= (smul r2 m1) m2))
(assert (= (in_subset m2) absent))
(assert (= (in_subset (smul r2 m1)) present))
(check-sat)
