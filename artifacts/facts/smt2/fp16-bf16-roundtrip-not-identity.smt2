; F:fp16-bf16-roundtrip-not-identity is REFUTED: this file asserts the NEGATION of
; that fact's `formal.statement`, and `sat` -- a concrete binary16 value the
; round trip through bfloat16 does not return -- is the result recorded in its
; evidence row.
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 5 11))
(assert (not (= ((_ to_fp 5 11) RNE ((_ to_fp 8 8) RNE x)) x)))
(check-sat)
