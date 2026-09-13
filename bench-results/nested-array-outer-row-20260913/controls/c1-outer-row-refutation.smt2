; EXPECT: REACH
; The gate map's `outer_read_over_write_on_a_nested_array_is_undecided` query,
; written inside this instrument's accepted fragment (the outer array is only
; ever the base of a select or of a store that is read).  It is the negation of
; the outer read-over-write axiom composed with an inner read, so it is unsat,
; and its refutation needs outer read-over-write and nothing else.  If the
; instrument cannot reach THIS, every zero it reports is uninterpretable.
(set-logic ALIA)
(declare-fun M () (Array Int (Array Int Int)))
(declare-fun r () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun o () Int)
(assert (= i j))
(assert (not (= (select (select (store M i r) j) o) (select r o))))
(check-sat)
