; QF_UF additive-closure conflict for finite-ideals-v0.
;
; The malformed subset has 2 present but 4 absent, while the Z/6Z addition
; table gives 2 + 2 = 4. Additive closure would require 2 + 2 to remain
; present, so the row is refuted by EUF over the fixed table facts.
(set-logic QF_UF)
(declare-sort R 0)
(declare-sort Membership 0)
(declare-fun present () Membership)
(declare-fun absent () Membership)
(declare-fun r2 () R)
(declare-fun r4 () R)
(declare-fun add (R R) R)
(declare-fun in_subset (R) Membership)
(assert (not (= present absent)))
(assert (= (in_subset r2) present))
(assert (= (add r2 r2) r4))
(assert (= (in_subset r4) absent))
(assert (= (in_subset (add r2 r2)) present))
(check-sat)
