; Negation of F:fp8-add-monotone-rne -- `unsat` is the result recorded in that
; fact's evidence row. Generated verbatim from the fact's own
; `formal.statement`, so the two cannot drift.
;
; `fp.leq` is false whenever either operand is NaN, so the antecedent already
; excludes NaN inputs; the two explicit `fp.isNaN` guards exclude the results
; (`x + (-x)` style cancellations are finite, but `(+oo) + (-oo)` is NaN).
(set-logic QF_FP)
(declare-const a (_ FloatingPoint 5 3))
(declare-const b (_ FloatingPoint 5 3))
(declare-const c (_ FloatingPoint 5 3))
(assert (not (=> (and (fp.leq a b)
                      (not (fp.isNaN (fp.add RNE a c)))
                      (not (fp.isNaN (fp.add RNE b c))))
                 (fp.leq (fp.add RNE a c) (fp.add RNE b c)))))
(check-sat)
