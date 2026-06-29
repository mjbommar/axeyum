; QF_UF composition-application consistency conflict for function-composition-v0.
;
; comp(a) is asserted to be g(f(a)); f(a)=b and g(b)=c force comp(a)=c by
; congruence and transitivity. The final assertion demands the opposite.
(set-logic QF_UF)
(declare-sort A 0)
(declare-sort B 0)
(declare-sort C 0)
(declare-fun a () A)
(declare-fun b () B)
(declare-fun c () C)
(declare-fun f (A) B)
(declare-fun g (B) C)
(declare-fun comp (A) C)
(assert (= (comp a) (g (f a))))
(assert (= (f a) b))
(assert (= (g b) c))
(assert (not (= (comp a) c)))
(check-sat)
