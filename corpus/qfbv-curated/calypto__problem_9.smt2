(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
    Sequential equivalence checking.
    Calypto Design Systems, Inc. <www.calypto.com>
  |)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun P_2 () (_ BitVec 8))
(declare-fun P_3 () (_ BitVec 9))
(declare-fun P_4 () (_ BitVec 8))
(assert (let ((?v_0 ((_ sign_extend 7) ((_ sign_extend 7) (bvshl (concat (_ bv0 4) P_3) (_ bv4 13)))))) (let ((?v_1 ((_ extract 14 0) (bvlshr (bvadd (bvadd (_ bv16 20) ((_ extract 19 0) (bvlshr (bvmul ((_ sign_extend 19) P_2) ?v_0) (_ bv7 27)))) ((_ extract 19 0) (bvlshr (bvadd (bvmul ((_ sign_extend 19) P_4) ?v_0) (_ bv64 27)) (_ bv7 27)))) (_ bv5 20))))) (not (= (ite (bvslt ?v_1 (_ bv32512 15)) (_ bv1 1) (_ bv0 1)) (ite (bvslt (_ bv255 15) ?v_1) (_ bv1 1) (_ bv0 1)))))))
(check-sat)
(exit)
