(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
    Sequential equivalence checking.
    Calypto Design Systems, Inc. <www.calypto.com>
  |)
(set-info :category "industrial")
(set-info :status unknown)
(declare-fun P_2 () (_ BitVec 64))
(declare-fun P_3 () (_ BitVec 64))
(assert (let ((?v_0 ((_ extract 51 0) P_2)) (?v_1 ((_ extract 51 0) P_3)) (?v_3 ((_ extract 31 0) P_3)) (?v_2 ((_ extract 31 0) P_2))) (not (= ((_ extract 63 0) (bvmul (concat (_ bv0 52) ?v_0) (concat (_ bv0 52) ?v_1))) (bvadd (bvshl (concat (_ bv0 32) ((_ extract 31 0) (bvadd (concat (_ bv0 1) (bvmul (concat (_ bv0 32) ((_ extract 19 0) (bvlshr ?v_0 (_ bv32 52)))) (concat (_ bv0 20) ?v_3))) (concat (_ bv0 1) (bvmul (concat (_ bv0 20) ?v_2) (concat (_ bv0 32) ((_ extract 19 0) (bvlshr ?v_1 (_ bv32 52))))))))) (_ bv32 64)) (bvmul (concat (_ bv0 32) ?v_2) (concat (_ bv0 32) ?v_3)))))))
(check-sat)
(exit)
