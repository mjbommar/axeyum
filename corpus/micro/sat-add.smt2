; origin: Axeyum hand-written micro corpus
; expected: sat
; pins: model replay for a unique QF_BV addition solution
(set-info :status sat)
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= (bvadd x (_ bv1 8)) (_ bv5 8)))
(check-sat)
