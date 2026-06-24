(set-logic QF_NRA)
(set-info :smt-lib-version 2.6)
(set-info :source |axeyum synthetic graduated corpus (scripts/gen-graduated-nra-nia.py)|)
(set-info :status unsat)
; STATUS-PROOF: x^4 is an even power, >= 0 over the reals; asserted < 0 -> infeasible (even-power non-negativity).
(declare-fun x () Real)

(assert (< (* x x x x) 0.0))
(check-sat)
