; EXPECT: SAT
; The SV-COMP memory model's own shape: an outer `store` whose written row is a
; UNIVERSALLY QUANTIFIED inner array, read back at a different outer index.  The
; quantifier ranges over rows that are never read, so the query is satisfiable.
;
; This is the fixture that would catch a rewrite which dropped the quantifier's
; binding of `v` while inlining -- an inlined alias that captured `v` would turn
; an unconstrained row into a constrained one and could flip this to `unsat`.
(set-logic ALIA)
(declare-fun M () (Array Int (Array Int Int)))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun o () Int)
(assert (not (= i j)))
(assert (forall ((v (Array Int Int)))
  (= (select (select (store M i v) j) o) (select (select M j) o))))
(assert (not (= (select (select M j) o) 0)))
(check-sat)
