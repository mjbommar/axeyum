; Negation of F:no-integer-square-is-minus-one. Recorded result: `unsat`, with a BARE
; uncertified evidence object -- see that fact's notes. Not an evidence row.
;
; This file is the negative control of scripts/check-smt-evidence-certified.py: it must
; stay genuinely unsatisfiable (so a verdict-only checker accepts it) and genuinely
; uncertified (so a certification-aware one must not). It replaced
; neg-barber-no-such-barber.smt2 on 2026-08-17, when that instance became certifiable.
(set-logic QF_NIA)
(declare-fun x () Int)
(assert (= (* x x) (- 1)))
(check-sat)
