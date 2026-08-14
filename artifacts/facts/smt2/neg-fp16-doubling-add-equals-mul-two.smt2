; Negation of F:fp16-doubling-add-equals-mul-two -- `unsat` is the result recorded
; in that fact's evidence row. Generated verbatim from the fact's own
; `formal.statement`, so the two cannot drift.
;
; `(fp #b0 #b10000 #b0000000000)` is the binary16 encoding of 2.0: biased
; exponent 16 = bias(15) + 1, zero stored fraction.
; `=` is SMT-LIB equality on the FloatingPoint sort (one NaN value, +0 and -0
; distinct) -- NOT `fp.eq`, which would make the claim vacuously weaker at NaN
; and stronger at the zeros.
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 5 11))
(assert (not (= (fp.add RNE x x) (fp.mul RNE (fp #b0 #b10000 #b0000000000) x))))
(check-sat)
