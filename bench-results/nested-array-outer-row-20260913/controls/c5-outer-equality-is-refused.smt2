; EXPECT: REFUSE
; Outer EXTENSIONALITY is the axiom currying does not have, and the accepted
; fragment excludes it by excluding every context in which two outer arrays are
; compared.  This fixture is unsat and its refutation needs exactly that axiom,
; so if the script ever rewrote it the reach number would be counting a file the
; surrogate is not entitled to speak about.
(set-logic ALIA)
(declare-fun M () (Array Int (Array Int Int)))
(declare-fun N () (Array Int (Array Int Int)))
(declare-fun r () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun o () Int)
(assert (= N (store M i r)))
(assert (= i j))
(assert (not (= (select (select N j) o) (select r o))))
(check-sat)
