(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
We give a counter-example for (x + 1 <= y) -> (x < y)
Contributed by Andreas Froehlich, Gergely Kovasznai, Armin Biere
Institute for Formal Models and Verification, JKU, Linz, 2013
source: http://fmv.jku.at/smtbench and "Efficiently Solving Bit-Vector Problems Using Model Checkers" by Andreas Froehlich, Gergely Kovasznai, Armin Biere. In Proc. 11th Intl. Workshop on Satisfiability Modulo Theories (SMT'13), pages 6-15, aff. to SAT'13, Helsinki, Finland, 2013.
|)
(set-info :category "crafted")
(set-info :status sat)
(declare-fun x () (_ BitVec 25489))
(declare-fun y () (_ BitVec 25489))
(assert (bvuge x y))
(assert (bvule (bvadd x (_ bv1 25489)) y))
(check-sat)
(exit)
