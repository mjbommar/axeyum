(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status sat)
(set-info :category "industrial")
(set-info :source |
  Generated using using the Low-Level Bounded Model Checker LLBMC.
  C files used in the paper: Florian Merz, Stephan Falke, Carsten Sinz: LLBMC: Bounded Model Checking of C and C++ Programs Using a Compiler IR. VSTTE 2012: 146-161
|)
(declare-fun addr_0x130ef30 () (_ BitVec 64))
(assert
(let ((?x1 (_ bv0 64)))
(let ((?x2 addr_0x130ef30))
(let (($x3 (= ?x2 ?x1)))
(let (($x4 (not $x3)))
$x4
))))
)
(check-sat)
(exit)
