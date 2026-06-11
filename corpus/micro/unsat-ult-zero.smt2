; origin: Axeyum hand-written micro corpus
; expected: unsat
; pins: unsigned less-than edge case where no BV value is below zero
(set-info :status unsat)
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (bvult x (_ bv0 8)))
(check-sat)
