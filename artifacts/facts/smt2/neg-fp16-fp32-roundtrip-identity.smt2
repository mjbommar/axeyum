; Negation of F:fp16-fp32-roundtrip-identity -- `unsat` is the result recorded in
; that fact's evidence row. Generated verbatim from the fact's own
; `formal.statement`, so the two cannot drift.
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 5 11))
(assert (not (= ((_ to_fp 5 11) RNE ((_ to_fp 8 24) RNE x)) x)))
(check-sat)
