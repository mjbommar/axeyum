; QF_UF associativity conflict for finite-monoids-v0.
;
; The malformed table has b*b=a, a*b=a, and b*a=b. Associativity on the
; failing triple (b,b,b) would require (b*b)*b = b*(b*b). Together with a != b,
; pure EUF congruence and transitivity refute the claim.
(set-logic QF_UF)
(declare-sort M 0)
(declare-fun a () M)
(declare-fun b () M)
(declare-fun mul (M M) M)
(assert (= (mul b b) a))
(assert (= (mul a b) a))
(assert (= (mul b a) b))
(assert (= (mul (mul b b) b) (mul b (mul b b))))
(assert (not (= a b)))
(check-sat)
