(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
Ivan Jager <aij+nospam@andrew.cmu.edu>

|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun t_147 () (_ BitVec 1))
(declare-fun t_146 () (_ BitVec 1))
(assert (= (_ bv1 1) (bvand (bvand (ite (= t_146 (_ bv1 1)) (_ bv1 1) (_ bv0 1)) (ite (= t_147 t_146) (_ bv1 1) (_ bv0 1))) (bvand (bvnot (bvnot t_146)) (bvand t_147 (_ bv1 1))))))
(check-sat)
(exit)
