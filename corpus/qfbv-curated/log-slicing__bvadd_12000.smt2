(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
Checking the soundness of the translation of bvadd to base operations (bitwise ones, equality, and slicing).
Contributed by Gergely Kovasznai, Andreas Froehlich, and Armin Biere.
Institute for Formal Models and Verification, JKU, Linz, 2013.
source: http://fmv.jku.at/smtbench and "Complexity of Fixed-Size Bit-Vector Logics" by Gergely Kovasznai, Andreas Froehlich, and Armin Biere. Submitted to the journal Theory of Computing Systems in 2013.
|)
(set-info :category "crafted")
(set-info :status unsat)
(declare-fun input1_0 () (_ BitVec 12000))
(declare-fun input2_1 () (_ BitVec 12000))
(declare-fun result_2 () (_ BitVec 12000))
(assert (= result_2 (bvadd input1_0 input2_1)))
(declare-fun bvadd_result_3 () (_ BitVec 12000))
(declare-fun cin_4 () (_ BitVec 12000))
(declare-fun cout_5 () (_ BitVec 12000))
(assert (= bvadd_result_3 (bvxor (bvxor input1_0 input2_1) cin_4)))
(assert (= cout_5 (bvor (bvor (bvand input1_0 input2_1) (bvand input1_0 cin_4)) (bvand input2_1 cin_4))))
(declare-fun concat_result_6 () (_ BitVec 12000))
(assert (= ((_ extract 11998 0) cout_5) ((_ extract 11999 1) concat_result_6)))
(assert (= (_ bv0 1) ((_ extract 0 0) concat_result_6)))
(assert (= cin_4 concat_result_6))
(assert (not (= result_2 bvadd_result_3)))
(check-sat)
(exit)
