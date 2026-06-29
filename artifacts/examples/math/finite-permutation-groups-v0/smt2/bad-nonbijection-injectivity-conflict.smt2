; QF_UF injectivity conflict for finite-permutation-groups-v0.
;
; The malformed self-map sends both point 1 and point 2 to image 1. A
; permutation must send distinct inputs to distinct images, so the fixed
; distinct-image claim contradicts the table equations.
(set-logic QF_UF)
(declare-sort P 0)
(declare-fun point1 () P)
(declare-fun point2 () P)
(declare-fun image1 () P)
(declare-fun bad (P) P)
(assert (not (= point1 point2)))
(assert (= (bad point1) image1))
(assert (= (bad point2) image1))
(assert (not (= (bad point1) (bad point2))))
(check-sat)
