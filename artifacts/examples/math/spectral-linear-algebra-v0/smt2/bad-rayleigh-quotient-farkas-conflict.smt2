; QF_LRA/Farkas obstruction for spectral-linear-algebra-v0.
;
; Finite replay computes the Rayleigh quotient of [1,1] for [[2,1],[1,2]]
; as 6/2 = 3. This artifact checks the malformed claim that the same quotient
; is 4.
(set-logic QF_LRA)
(declare-const rayleigh_quotient Real)
(assert (= rayleigh_quotient 3))
(assert (= rayleigh_quotient 4))
(check-sat)
