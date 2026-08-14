; Negation of F:fp32-doubling-add-equals-mul-two -- `unsat` is the result recorded
; in that fact's evidence row. Generated verbatim from the fact's own
; `formal.statement`, so the two cannot drift.
;
; binary32. 2^32 inputs is beyond any exhaustive route, so this file is decided
; SYMBOLICALLY -- the honest distinction this fact exists to record against its
; binary16 sibling.
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(assert (not (= (fp.add RNE x x)
                (fp.mul RNE (fp #b0 #b10000000 #b00000000000000000000000) x))))
(check-sat)
