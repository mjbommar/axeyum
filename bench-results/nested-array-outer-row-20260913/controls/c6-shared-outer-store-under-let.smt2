; EXPECT: REACH
; The generator's sharing idiom: the outer `store` is bound by `let` and read
; twice.  ADR-1971's instrument INLINES such a binding rather than refusing it,
; which is worth 2 accepted files on ALIA's winnable list; this fixture is what
; makes the inlining observable rather than trusted, because the refutation
; needs BOTH reads of the shared row to see the same write.
(set-logic ALIA)
(declare-fun M () (Array Int (Array Int Int)))
(declare-fun r () (Array Int Int))
(declare-fun i () Int)
(declare-fun o () Int)
(declare-fun p () Int)
(assert (let ((w (store M i r)))
  (not (and (= (select (select w i) o) (select r o))
            (= (select (select w i) p) (select r p))))))
(check-sat)
