; The concrete counterexample recorded in F:fp8-add-not-associative, pinned as a
; GROUND formula: no free symbols, so a `sat` verdict here is direct evaluation
; of IEEE-754 fp8 E5M2 arithmetic, not a search.
;
;   a = b = 0x01 = the fp8 E5M2 subnormal 2^-16
;   c     = 0x08 = the normal value 2^-13
;
;   a+b        = 2^-15                     (exact)
;   (a+b)+c    = 2^-13 * 1.25  = 0x09      (exact)
;   b+c        = 2^-13 * 1.125 -> tie, RNE rounds to even -> 2^-13 = 0x08
;   a+(b+c)    = 2^-13 * 1.125 -> tie again              -> 2^-13 = 0x08
;
; so (a+b)+c = 0x09 while a+(b+c) = 0x08. Expected verdict: sat.
(set-logic QF_FP)
(assert (let ((a (fp #b0 #b00000 #b01))
              (b (fp #b0 #b00000 #b01))
              (c (fp #b0 #b00010 #b00)))
  (and (not (= (fp.add RNE (fp.add RNE a b) c)
               (fp.add RNE a (fp.add RNE b c))))
       (= (fp.add RNE (fp.add RNE a b) c) (fp #b0 #b00010 #b01))
       (= (fp.add RNE a (fp.add RNE b c)) (fp #b0 #b00010 #b00)))))
(check-sat)
