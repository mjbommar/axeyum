; F:fp8-add-not-associative is REFUTED: this file asserts the NEGATION of that
; fact's `formal.statement`, and `sat` -- a concrete counterexample triple -- is
; the result recorded in its evidence row.
;
; Format is OCP fp8 E5M2, SMT-LIB `(_ FloatingPoint 5 3)`: the IEEE-754
; conformant 8-bit layout. (E4M3 is NOT IEEE -- no infinities, all-ones NaN --
; and is deliberately not used here.)
(set-logic QF_FP)
(declare-const a (_ FloatingPoint 5 3))
(declare-const b (_ FloatingPoint 5 3))
(declare-const c (_ FloatingPoint 5 3))
(assert (not (= (fp.add RNE (fp.add RNE a b) c)
                (fp.add RNE a (fp.add RNE b c)))))
(check-sat)
