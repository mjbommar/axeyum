; The concrete counterexample recorded in F:fp16-bf16-roundtrip-not-identity,
; pinned as a GROUND formula: no free symbols, so a `sat` verdict here is direct
; evaluation, not a search.
;
;   x = 0x0101 = the binary16 subnormal 257 * 2^-24
;
; bfloat16 keeps 8 significand bits; 257 needs 9, so the narrowing leg rounds to
; 256 * 2^-24 and the widening leg back to binary16 cannot recover the lost bit.
; Expected verdict: sat.
(set-logic QF_FP)
(assert (let ((x (fp #b0 #b00000 #b0100000001)))
  (and (not (= ((_ to_fp 5 11) RNE ((_ to_fp 8 8) RNE x)) x))
       (= ((_ to_fp 5 11) RNE ((_ to_fp 8 8) RNE x)) (fp #b0 #b00000 #b0100000000)))))
(check-sat)
