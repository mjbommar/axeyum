; EXPECT: SAT
; The adversarial direction.  Writing row `r` at outer index `i` says nothing
; about outer index `j` when `i` and `j` are unconstrained, so the two reads may
; differ and this query is satisfiable.  A surrogate that reported `unsat` here
; would be relaxing the ite guard of the read-over-write expansion -- the exact
; defect that makes a refutation-counting instrument overstate its reach.
(set-logic ALIA)
(declare-fun M () (Array Int (Array Int Int)))
(declare-fun r () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun o () Int)
(assert (not (= (select (select (store M i r) j) o) (select r o))))
(check-sat)
