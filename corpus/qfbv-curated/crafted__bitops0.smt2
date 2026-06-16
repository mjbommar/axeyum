(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
Hand-crafted bit-vector benchmarks.  Some are from the SVC benchmark suite.
Contributed by Vijay Ganesh (vganesh@stanford.edu).  Translated into SMT-LIB
format by Clark Barrett using CVC3.

|)
(set-info :category "crafted")
(set-info :status unsat)
(declare-fun y () (_ BitVec 1))
(declare-fun x () (_ BitVec 2))
(declare-fun z () (_ BitVec 4))
(declare-fun d () (_ BitVec 3))
(declare-fun e () (_ BitVec 4))
(declare-fun f () (_ BitVec 3))
(declare-fun a () (_ BitVec 5))
(declare-fun b () (_ BitVec 5))
(declare-fun c () (_ BitVec 5))
(assert (let ((?v_0 (bvadd (_ bv7 5) b)) (?v_1 (bvadd a b)) (?v_2 (concat (_ bv0 1) x))) (not (and (and (and (and (and (and (and (and (and (not (= y (bvnot y))) (= ((_ extract 6 6) (bvnot (concat (concat x (_ bv5 3)) z))) (_ bv0 1))) (=> (= ((_ extract 7 2) (bvnot (concat (concat d e) (_ bv2 3)))) (concat d f)) (ite (= e (_ bv0 4)) (and (= d (_ bv3 3)) (= f (_ bv7 3))) (=> (= e (_ bv15 4)) (and (= d (_ bv4 3)) (= f (_ bv1 3))))))) (not (= ?v_0 (bvnot ?v_0)))) (not (= ?v_1 (bvnot ?v_1)))) (=> (= ?v_1 (bvadd a c)) (= b c))) (= (bvadd x (bvadd (bvnot x) (_ bv1 2))) (_ bv0 2))) (=> (= ((_ extract 3 3) z) (_ bv0 1)) (not (= (bvadd (_ bv1 4) (bvadd (_ bv2 4) (bvadd (_ bv4 4) z))) (_ bv0 4))))) (= ((_ extract 5 5) (bvadd (_ bv10 6) (_ bv21 6))) (_ bv0 1))) (=> (= ((_ extract 1 1) x) (_ bv0 1)) (= ((_ extract 2 2) (bvadd ?v_2 ?v_2)) (_ bv0 1)))))))
(check-sat)
(exit)
