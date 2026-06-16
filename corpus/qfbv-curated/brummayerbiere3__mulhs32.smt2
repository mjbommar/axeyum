(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
High-order half of product algorithm mulhs(u, v), (signed context) 
From the book "Hacker's delight" by Henry S. Warren, Jr., page 132
We verify that it indeed computes the high-order half.

Contributed by Robert Brummayer (robert.brummayer@gmail.com)
|)
(set-info :category "crafted")
(set-info :status unsat)
(declare-fun u () (_ BitVec 32))
(declare-fun v () (_ BitVec 32))
(assert (let ((?v_3 (bvand u (_ bv65535 32))) (?v_0 ((_ zero_extend 27) (_ bv16 5)))) (let ((?v_2 (bvashr u ?v_0)) (?v_4 (bvand v (_ bv65535 32))) (?v_1 (bvashr v ?v_0))) (let ((?v_5 (bvadd (bvmul ?v_2 ?v_4) (bvlshr (bvmul ?v_3 ?v_4) ?v_0)))) (not (= (bvnot (ite (= (bvadd (bvmul ?v_2 ?v_1) (bvadd (bvashr (bvadd (bvmul ?v_3 ?v_1) (bvand ?v_5 (_ bv65535 32))) ?v_0) (bvashr ?v_5 ?v_0))) ((_ extract 63 32) (bvmul ((_ sign_extend 32) u) ((_ sign_extend 32) v)))) (_ bv1 1) (_ bv0 1))) (_ bv0 1)))))))
(check-sat)
(exit)
