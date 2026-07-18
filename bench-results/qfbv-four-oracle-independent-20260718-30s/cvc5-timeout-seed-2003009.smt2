(set-logic QF_BV)
(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 32))
(assert (or (= ((_ extract 35 4) ((_ sign_extend 14) (bvshl (_ bv4073162 22) (_ bv2394321 22)))) ((_ extract 31 0) (_ bv1303039381 32))) (distinct ((_ extract 31 0) (_ bv20980091270 35)) (bvadd (bvsdiv (concat (_ bv50356091 27) (_ bv14 5)) (bvsmod (_ bv3706944386 32) x)) (bvmul (concat (_ bv339615847 29) (_ bv2 3)) (bvlshr x x))))))
(assert (bvult y ((_ zero_extend 17) (_ bv22135 15))))
(check-sat)
(exit)

